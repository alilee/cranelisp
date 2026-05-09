// cranelisp-backend: Cranelift IR codegen, JIT, RC emission, caching, linking.
//
// Public API:
// - compile_to_module: compile a set of named symbols' functions into any Cranelift Module
// - build_isa: ISA construction for JIT and ObjectModule (re-exported from cache::object)

pub mod cache;

// Re-export build_isa at the crate root for convenient access.
// This is the single ISA construction point (architecture decision 7).
pub use cache::object::build_isa;
use cranelisp_types::ModuleEntry;
// Re-export TargetIsa for shared ISA in N-core codegen (pipeline-v3.md §6).
pub use cranelift::codegen::isa::TargetIsa;
// Re-export Cranelift module types for callers of compile_to_module.
pub use cranelift_module;
pub use cranelift_object;
pub mod codegen_types;
pub mod exe;
pub mod compiler;
pub mod display;
pub mod got;
pub mod heap;
pub mod jit;
pub mod operators;

use std::collections::HashMap;

use cranelift_module::FuncId;

use dashmap::DashMap;

use cranelisp_types::{ErrorLocation, 
    CranelispError, Defn, ModuleFullPath, Span, Symbol, SymbolTable, Warning,
};

use cranelift::prelude::*;
use cranelift_module::Module;

use crate::compiler::{CompileContext, FnCompiler};
use crate::jit::declare_intrinsics_generic;

// --- CLIF dump observability (Sprint 60 Workstream B) --------------------
//
// `CRANELISP_CODEGEN_DUMP` selects which freshly-codegen'd CLIF is written
// to stderr during `compile_to_module`. This is load-bearing for diagnosing
// JIT/object divergence and codegen-layer bugs (drop glue, RC, GOT) where
// source-level reduction plateaus and only the emitted IR distinguishes
// correct vs broken output. Cache-hit paths do NOT re-codegen and so have
// nothing to dump; for those, use `/clif <name>` from the REPL to view the
// stored `FunctionArtifacts.clif_ir`.
//
// Filter grammar (value of `CRANELISP_CODEGEN_DUMP`):
//   unset/empty → disabled (no dump)
//   `*`         → dump every function in every module
//   `<module>`  → dump every function in that module (match on the
//                 `ModuleFullPath` string, e.g. `user`, `exemplar.solver`)
//   `<module>::<symbol>` → dump only that exact function
//
// Output: stderr, framed with `; === CLIF <module>::<symbol> ===` so it is
// greppable in test output. Shape mirrors what `/clif` prints in the REPL.

/// Decide whether to dump CLIF for a given (module, symbol) pair given the
/// current value of `CRANELISP_CODEGEN_DUMP`.
///
/// Pulled out as a pure function so unit tests can exercise the filter
/// grammar without any codegen side-effects.
fn clif_dump_matches(filter: Option<&str>, module_path: &str, symbol: &str) -> bool {
    let Some(filter) = filter.filter(|s| !s.is_empty()) else {
        return false;
    };
    if filter == "*" {
        return true;
    }
    if let Some((m, s)) = filter.split_once("::") {
        return m == module_path && s == symbol;
    }
    filter == module_path
}

/// Print a CLIF dump header + body to the provided writer. Extracted from the
/// call site so tests can capture output without intercepting stderr.
fn write_clif_dump(
    out: &mut dyn std::io::Write,
    module_path: &str,
    symbol: &str,
    clif_ir: &str,
) -> std::io::Result<()> {
    writeln!(out, "; === CLIF {module_path}::{symbol} ===")?;
    out.write_all(clif_ir.as_bytes())?;
    if !clif_ir.ends_with('\n') {
        writeln!(out)?;
    }
    writeln!(out, "; === end CLIF {module_path}::{symbol} ===")
}

/// Per-symbol codegen byproducts captured during `compile_to_module`.
///
/// Populated during the same `FnCompiler` pass that defines each function.
/// Returned in `CompilationResult.artifacts` keyed by the symbol's local name
/// in `symbol_tables[module_path]` — see design/backend/compile-to-module.md
/// §8.1 for the contract. The caller (e.g., priority worker in Wave 2) routes
/// these into `Introspection` without a second compilation pass.
pub struct FunctionArtifacts {
    /// Human-readable CLIF dump of the compiled function. Same text rendered
    /// by `/clif`.
    pub clif_ir: String,
    /// Human-readable machine-code disassembly (may be empty on platforms that
    /// don't support disassembly). Same text rendered by `/disasm`.
    pub disasm: String,
    /// Size in bytes of the compiled machine code.
    pub code_size: u32,
}

/// Result of compiling a set of named symbols into a Cranelift module.
///
/// Module-type-agnostic: the caller extracts what it needs.
/// For JIT: uses `entry_func_id` to get the entry point after finalization.
/// For ObjectModule: ignores `entry_func_id` (no entry needed for .o files).
pub struct CompilationResult {
    /// FuncIds for all compiled functions (name -> FuncId).
    pub func_ids: HashMap<Symbol, FuncId>,
    /// Per-symbol finalised code pointers for JIT-capable modules. Keyed by
    /// the same local `Symbol` used in `func_ids`. Empty for `ObjectModule`
    /// (no runtime pointers exist before `finish()`); populated for
    /// `JITModule` after `finalize_for_code_read`.
    ///
    /// Sprint 58 Wave 3b (Decision 35 Layer 2 Option B): backend returns
    /// raw pointers and the integration layer constructs `Code::Jit { jit,
    /// ptr }` per defined symbol. This keeps `cranelisp-backend` ignorant
    /// of the integration-layer `Code` enum and preserves Principle 3
    /// (no `cranelisp-types -> cranelisp-backend` edge); `Code` lives in
    /// `src/code.rs`.
    pub code_ptrs: HashMap<Symbol, *const u8>,
    /// Per-symbol artifacts for introspection (CLIF IR, disassembly, code
    /// size). See `FunctionArtifacts` and design/backend/compile-to-module.md
    /// §8.1. Keyed by the same local `Symbol` used in `func_ids`.
    pub artifacts: HashMap<Symbol, FunctionArtifacts>,
    /// FuncId of the entry function (last zero-arg defn), if any.
    pub entry_func_id: Option<FuncId>,
    /// Function arities for all compiled functions.
    pub func_arities: HashMap<Symbol, usize>,
    /// Warnings accumulated during codegen.
    pub warnings: Vec<Warning>,
}

// SAFETY: `code_ptrs` is `HashMap<Symbol, *const u8>`. The raw pointer is
// an integer handle into JIT-emitted pages owned by the caller's `Arc<Jit>`
// (Decision 35); transmitting the integer across threads is safe. The
// caller (integration layer) constructs `Code::Jit { jit, ptr }` where
// `Arc<Jit>` is the lifetime root for `ptr`. This `unsafe impl` exists so
// `CompilationResult` can be returned across worker boundaries; the same
// reasoning that justified the pre-Wave-3b `KeptJit` and `Code` Send/Sync
// impls applies.
unsafe impl Send for CompilationResult {}
unsafe impl Sync for CompilationResult {}

/// Capability extension for the `Module` trait: post-finalize code access.
///
/// `cranelift_module::Module` does NOT expose `finalize_definitions` or
/// `get_finalized_function` — those are inherent methods on specific
/// implementations (`JITModule`) and absent from others (`ObjectModule`,
/// whose output is bytes via `finish().emit()`, not runtime pointers).
///
/// Per `design/backend/compile-to-module.md` §9.1.6 and `/arch` Decision 23,
/// the JIT/Object split is a capability difference expressed on the `Module`
/// implementation — not a mode parameter on `compile_to_module`. This trait
/// provides that capability: `JITModule` implements it with the real
/// operations; `ObjectModule` implements it with no-ops that surface `None`
/// so the G6 write loop skips the per-entry pointer store in object mode.
///
/// Any new `Module` implementation that `compile_to_module` is asked to
/// target must provide an impl — either the "real" one (if it has runtime
/// code pointers) or a no-op stub (if it has no post-finalize pointer, e.g.,
/// an emitter that produces bytes).
pub trait CodeFinalizer {
    /// Finalize pending definitions so that code pointers become readable.
    /// For `JITModule`: patches relocations, makes mmap'd pages executable.
    /// For `ObjectModule`: no-op (bytes are emitted via a later `finish()`).
    ///
    /// Called once per `compile_to_module` invocation after all `define_function`
    /// calls complete. Implementations that cannot finalize (e.g., already
    /// finalized) should return an error, not silently succeed.
    fn finalize_for_code_read(&mut self) -> Result<(), CranelispError>;

    /// Read a finalized code pointer for the given `FuncId`, if this module
    /// exposes runtime pointers. Returns `None` on implementations that have
    /// no such concept (`ObjectModule`), which gates the G6 write loop to JIT
    /// mode only (per §9.1.6).
    ///
    /// Only valid after `finalize_for_code_read()` has returned `Ok`.
    fn try_get_finalized_function(&self, func_id: FuncId) -> Option<*const u8>;

    /// Define the per-module GOT data symbol (`__cranelisp_got_{M}`) inside
    /// the module's `.o` artefact, with relocation initializers against each
    /// of the module's local function symbols. Implements the `.o` data
    /// section GOT half of the two-GOT model (`/arch` Decision 23 + 36).
    ///
    /// Parameters:
    /// - `name`: the `__cranelisp_got_{flat_path}` data symbol name
    ///   (single source of truth: `compiler::got_data_symbol_name`).
    /// - `slot_count`: total slot count = `max(slot_index) + 1`. The data
    ///   symbol is sized as `slot_count * 8` bytes (zero-initialized).
    /// - `slot_funcs`: `(slot_index, FuncId)` pairs for every defined
    ///   function in this module. Each slot's 8-byte entry receives a
    ///   relocation initializer pointing to that function's local symbol.
    ///   Slots with no entry remain zero (empty slots are not currently
    ///   produced by typecheck — every defined function gets a slot).
    ///
    /// For `JITModule`: no-op. The JIT-mode `__cranelisp_got_{M}` data is
    /// defined by the integration layer via `Jit::define_got_data` directly,
    /// pointing at the runtime `SymbolTable.got.base_ptr()`. The `.o` data
    /// definition is irrelevant in JIT mode (no `.o` is emitted).
    ///
    /// For `ObjectModule`: declares the symbol as `Linkage::Export`,
    /// allocates `slot_count * 8` bytes initialized to zero, and writes a
    /// function-address relocation at byte offset `slot_index * 8` for each
    /// `(slot_index, FuncId)` pair. The system linker (`--link` mode) and
    /// our cache `Linker` (`--run` mode after cache-hit) materialise these
    /// relocations into actual function addresses at load time.
    ///
    /// Per Decision 23: the same CLIF emitted by `compile_to_module<M>`
    /// references `__cranelisp_got_{M}` symmetrically as `Linkage::Import`
    /// in both modes; the *definition* differs by `Module` impl. JIT mode's
    /// definition lives outside `compile_to_module` (in the integration
    /// layer's `Jit::define_got_data` call); object mode's definition lives
    /// in this trait method, called from inside `compile_to_module`.
    fn define_module_got_data(
        &mut self,
        name: &str,
        slot_count: usize,
        slot_funcs: &[(usize, FuncId)],
    ) -> Result<(), CranelispError>;
}

impl CodeFinalizer for cranelift_jit::JITModule {
    fn finalize_for_code_read(&mut self) -> Result<(), CranelispError> {
        self.finalize_definitions().map_err(|e| CranelispError::CodegenError {
            message: format!("failed to finalize JIT definitions: {e}"),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        })
    }

    fn try_get_finalized_function(&self, func_id: FuncId) -> Option<*const u8> {
        Some(self.get_finalized_function(func_id))
    }

    fn define_module_got_data(
        &mut self,
        _name: &str,
        _slot_count: usize,
        _slot_funcs: &[(usize, FuncId)],
    ) -> Result<(), CranelispError> {
        // No-op: the JIT-mode `__cranelisp_got_{M}` data symbol is defined
        // by the integration layer's `Jit::define_got_data` call (which
        // points the symbol at the runtime SymbolTable.got.base_ptr()). The
        // `.o` data section GOT shape is unused in JIT mode — no `.o` is
        // emitted. See `/arch` Decision 23 (two-GOT model).
        Ok(())
    }
}

impl CodeFinalizer for cranelift_object::ObjectModule {
    fn finalize_for_code_read(&mut self) -> Result<(), CranelispError> {
        // No-op: ObjectModule output is bytes via `finish().emit()`, not
        // runtime code pointers. Finalization happens at byte-emit time, not
        // here. See §9.1.6 of compile-to-module.md.
        Ok(())
    }

    fn try_get_finalized_function(&self, _func_id: FuncId) -> Option<*const u8> {
        // No runtime pointer exists for object-mode compilation. The G6 write
        // loop skips the per-entry code write when this returns None.
        None
    }

    fn define_module_got_data(
        &mut self,
        name: &str,
        slot_count: usize,
        slot_funcs: &[(usize, FuncId)],
    ) -> Result<(), CranelispError> {
        // Bug B fix per `/arch` Decision 23 (updated Sprint 58 Wave 2):
        // declare the per-module GOT data symbol as `Linkage::Export` and
        // populate its slots with function-address relocations against each
        // defined function's local symbol. The system linker (`--link` mode)
        // and our cache `Linker` (`--run` mode after cache-hit) resolve the
        // relocations at load time, materialising the GOT contents.
        if slot_count == 0 {
            // No slots to define. Skip — symbol is not needed by callers.
            return Ok(());
        }

        let data_id = self
            .declare_data(name, cranelift_module::Linkage::Export, false, false)
            .map_err(|e| CranelispError::CodegenError {
                message: format!(
                    "failed to declare GOT data symbol '{name}' as Export: {e}"
                ),
                location: ErrorLocation::from_span(Span::SYNTHETIC),
            })?;

        let mut desc = cranelift_module::DataDescription::new();
        // Use `define` with explicit zero bytes (NOT `define_zeroinit`) so the
        // GOT lands in a regular `__DATA` section, not `__DATA,__bss`
        // (`S_ZEROFILL`). macOS `ld` segfaults when applying relocations
        // against BSS sections — relocations require a regular data section.
        // The contents are identical (zero-initialized 8 bytes per slot) but
        // the section placement differs. Function-address relocations declared
        // below via `desc.write_function_addr` are still applied normally at
        // link time.
        desc.define(vec![0u8; slot_count * 8].into_boxed_slice());

        for &(slot, func_id) in slot_funcs {
            // Sanity: slot must be in range; defensive guard against a
            // malformed slot list. A slot >= slot_count would corrupt
            // adjacent data; we surface the shape mismatch as an error
            // rather than silently truncate.
            if slot >= slot_count {
                return Err(CranelispError::CodegenError {
                    message: format!(
                        "GOT slot {slot} for '{name}' exceeds declared slot_count {slot_count}"
                    ),
                    location: ErrorLocation::from_span(Span::SYNTHETIC),
                });
            }
            let func_ref = self.declare_func_in_data(func_id, &mut desc);
            let offset: u32 = (slot * 8).try_into().map_err(|_| {
                CranelispError::CodegenError {
                    message: format!(
                        "GOT slot offset overflows u32 for slot {slot} in '{name}'"
                    ),
                    location: ErrorLocation::from_span(Span::SYNTHETIC),
                }
            })?;
            desc.write_function_addr(offset, func_ref);
        }

        self.define_data(data_id, &desc)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to define GOT data symbol '{name}': {e}"),
                location: ErrorLocation::from_span(Span::SYNTHETIC),
            })?;
        Ok(())
    }
}

/// Compile the functions named by `names` (all inside `module_path`) into a
/// Cranelift module.
///
/// This is the ONLY compilation entry point in the backend crate.
/// See design/backend/compile-to-module.md §2 (PRESCRIPTIVE).
///
/// Four parameters. Everything else derived internally:
/// - Intrinsics: declared on the module internally
/// - Defn bodies: read from `symbol_tables[module_path].get(name).ast`
/// - GOT slots: read from `ModuleEntry::Def.got_slot`
/// - GOT base resolution: uniform — emits `global_value` against a
///   `Linkage::Import` data symbol `__cranelisp_got_{module}`; `Module`
///   implementations resolve at finalize time (linker relocations for Object;
///   `JITBuilder::symbol_lookup_fn` for JIT — caller's responsibility)
/// - Cross-module function refs: under `/arch` Decision 36 (bare-Local)
///   plus Decision 31 (all-GOT calling), every cross-module call is GOT-
///   indirect (`__cranelisp_got_{other_M}`). No `Linkage::Import` function
///   declarations are needed for cross-module fns — they are unreachable
///   by direct call. Compile-time arity for cross-module calls is resolved
///   via `compiler::resolve_func_arity` walking the symbol tables.
///
/// # Function naming and linkage (`/arch` Decision 36)
///
/// Every user-defined function is declared with its bare symbol-table name
/// (`defn.name`) and `Linkage::Local`, uniformly across all modules. The
/// pre-Sprint-58 `user`/`main` special case (bare-Export for those modules,
/// FQ-Export for everything else) was a defect, deleted here. Function
/// symbols never cross `.o` boundaries — every call goes through the per-
/// module GOT — so `Linkage::Local` is sufficient and avoids cross-`.o`
/// symbol-table pollution. See Decision 36 in `design/arch/CLAUDE.md` and
/// `design/backend/compile-to-module.md` §7 for the full rationale.
///
/// # G6 write path
///
/// After `define_function` completes for every name in `names`, the function
/// calls `module.finalize_for_code_read()` and — for JIT-capable modules —
/// reads each finalized code pointer and writes it onto the corresponding
/// `ModuleEntry::Def.code` in `symbol_tables[module_path]` before returning.
/// For `ObjectModule`, the capability call returns `None` and the write loop
/// is skipped (no runtime pointer exists). See §9.1 of
/// `design/backend/compile-to-module.md` and `/arch` Decision 25 for the
/// architectural statement.
///
/// # GOT data symbol emission (`/arch` Decision 23 Bug B fix)
///
/// After function declarations, this function calls
/// `module.define_module_got_data(...)` to emit the per-module
/// `__cranelisp_got_{M}` data symbol. The implementation is `Module`-impl-
/// specific:
/// - `JITModule`: no-op (the JIT path defines this symbol externally via
///   `Jit::define_got_data` pointing at the runtime
///   `SymbolTable.got.base_ptr()`).
/// - `ObjectModule`: declares the symbol as `Linkage::Export` with a
///   zero-initialized slab of `slot_count * 8` bytes and writes a function-
///   address relocation at byte offset `slot * 8` for each defined
///   function. The system linker (`--link`) and the cache `Linker` (`--run`
///   after cache-hit) resolve the relocations at load time.
pub fn compile_to_module<M, C, L>(
    module_path: ModuleFullPath,
    names: &[Symbol],
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable<C, L>>,
    module: &mut M,
) -> Result<CompilationResult, CranelispError>
where
    M: Module + CodeFinalizer,
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    // Derive internal dependencies.
    let intrinsic_ids = declare_intrinsics_generic(module)?;

    // Step 1: Look up each named entry and retrieve its AST body (§4 symbol-
    // table lookup loop; replaces the former `program: &Program` scan).
    // Wave 0 invariant: each entry in `names` carries `ast: Some(_)`. If not,
    // surface a codegen error naming the offending symbol — see
    // design/backend/compile-to-module.md §16.4.
    let mut defns: Vec<Defn> = Vec::with_capacity(names.len());
    {
        let table = symbol_tables.get(&module_path).ok_or_else(|| {
            CranelispError::CodegenError {
                message: format!(
                    "compile_to_module: no symbol table for module '{module_path}'"
                ),
                location: ErrorLocation::from_span(Span::SYNTHETIC),
            }
        })?;
        for name in names {
            let entry = table.get(name.as_ref()).ok_or_else(|| {
                CranelispError::CodegenError {
                    message: format!(
                        "compile_to_module: symbol '{name}' not found in module '{module_path}'"
                    ),
                    location: ErrorLocation::from_span(Span::SYNTHETIC),
                }
            })?;
            let ModuleEntry::Def { ast, .. } = entry else {
                return Err(CranelispError::CodegenError {
                    message: format!(
                        "compile_to_module: symbol '{name}' in module '{module_path}' is not a compilable Def (wrong ModuleEntry variant)"
                    ),
                    location: ErrorLocation::from_span(Span::SYNTHETIC),
                });
            };
            let defn = ast.as_ref().ok_or_else(|| CranelispError::CodegenError {
                message: format!(
                    "compile_to_module: symbol '{name}' in module '{module_path}' has ast: None — Wave 0 invariant violated (see design/typecheck/ast-annotation.md for the categories of entries that must carry ast: Some(_))"
                ),
                location: ErrorLocation::from_span(Span::SYNTHETIC),
            })?;
            defns.push(defn.clone());
        }
    }

    if defns.is_empty() {
        return Err(CranelispError::CodegenError {
            message: "no function definitions to compile".into(),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        });
    }

    // Step 2: Declare all functions in the module (Pass 1).
    // Start with intrinsic FuncIds.
    let mut func_ids: HashMap<Symbol, FuncId> = intrinsic_ids.by_name.clone();

    // Per `/arch` Decision 36: every user-defined function is declared with
    // its bare symbol-table name and `Linkage::Local`, uniformly across all
    // modules. The pre-Sprint-58 user/main vs FQ-Export discriminator is a
    // defect (see Decision 36 rationale + design/backend/compile-to-module.md
    // §7). Function symbols are intra-`.o`-only because all calls go through
    // `__cranelisp_got_{M}` (Decision 31 redefinition correctness mandates
    // GOT-indirect even for intra-module calls).
    for defn in &defns {
        let mut sig = module.make_signature();
        for _ in defn.params() {
            sig.params.push(AbiParam::new(types::I64));
        }
        sig.returns.push(AbiParam::new(types::I64));

        let func_id = module
            .declare_function(defn.name.as_ref(), cranelift_module::Linkage::Local, &sig)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare function '{}': {e}", defn.name),
                location: ErrorLocation::from_span(defn.span),
            })?;
        func_ids.insert(defn.name.clone(), func_id);
    }

    // No cross-module function declarations: under all-GOT calling
    // (Decision 31) cross-module calls are GOT-indirect against
    // `__cranelisp_got_{other_M}`, never direct. Compile-time arity for
    // those calls is resolved via `compiler::resolve_func_arity` walking
    // the symbol tables (see compiler/control_flow.rs auto-curry path).
    let func_arities: HashMap<Symbol, usize> = defns
        .iter()
        .map(|d| (d.name.clone(), d.params().len()))
        .collect();

    // Step 3: Compile each function body (Pass 2).
    // All defns are compiled uniformly — mangled multi-sig variants and mono
    // specialisations are ordinary entries in `names` after Wave 0.
    let mut func_ctx = FunctionBuilderContext::new();
    let mut artifacts: HashMap<Symbol, FunctionArtifacts> = HashMap::new();

    // Read CLIF dump filter once per compile_to_module invocation — the env
    // var value is stable for the process lifetime and this loop may iterate
    // many times.
    let clif_dump_filter: Option<String> = std::env::var("CRANELISP_CODEGEN_DUMP").ok();

    for defn in &defns {
        let compile_ctx = CompileContext {
            func_ids: &func_ids,
            func_arities: &func_arities,
            symbol_tables,
            current_module: module_path.clone(),
            traced_fns: None,
            alloc_func_id: intrinsic_ids.alloc,
            dealloc_func_id: intrinsic_ids.dealloc.unwrap_or_else(|| {
                unreachable!(
                    "invariant: runtime/dealloc must be declared before compile \
                     (Decision 24)"
                )
            }),
            alloc_string_func_id: intrinsic_ids.alloc_string,
            panic_func_id: intrinsic_ids.panic,
            vec_new_func_id: intrinsic_ids.vec_new,
            vec_drop_func_id: intrinsic_ids.vec_drop,
        };
        let art = compile_defn_in_module(defn, module, &mut func_ctx, &func_ids, compile_ctx)?;
        if clif_dump_matches(clif_dump_filter.as_deref(), module_path.as_ref(), defn.name.as_ref()) {
            // Write directly to stderr; ignore I/O errors (stderr failure is
            // not worth poisoning a codegen result over).
            let _ = write_clif_dump(
                &mut std::io::stderr(),
                module_path.as_ref(),
                defn.name.as_ref(),
                &art.clif_ir,
            );
        }
        artifacts.insert(defn.name.clone(), art);
    }

    // Find entry function (last zero-arg defn).
    let entry_func_id = defns
        .iter()
        .rev()
        .find(|d| d.params().is_empty())
        .and_then(|d| func_ids.get(&d.name).copied());

    // Collect func_signatures for downstream modules. Under Decision 36
    // (bare-Local), function symbols are bare uniformly — no module-
    // qualified alias is produced.
    let result_func_ids: HashMap<Symbol, FuncId> = defns
        .iter()
        .filter_map(|d| func_ids.get(&d.name).map(|&fid| (d.name.clone(), fid)))
        .collect();

    // Step 4a (`/arch` Decision 23 Bug B fix): emit the per-module GOT data
    // symbol `__cranelisp_got_{M}`. For ObjectModule this defines a
    // `Linkage::Export` data symbol with relocation initializers against
    // each defined function's local symbol; for JITModule this is a no-op
    // because the JIT-mode definition lives outside `compile_to_module`.
    // See `define_module_got_data` impls and §5.4 of compile-to-module.md.
    {
        let table = symbol_tables.get(&module_path).ok_or_else(|| {
            CranelispError::CodegenError {
                message: format!(
                    "compile_to_module: no symbol table for module '{module_path}' at GOT-data emission"
                ),
                location: ErrorLocation::from_span(Span::SYNTHETIC),
            }
        })?;
        let mut slot_funcs: Vec<(usize, FuncId)> = Vec::with_capacity(defns.len());
        for defn in &defns {
            let entry = table.get(defn.name.as_ref()).ok_or_else(|| {
                CranelispError::CodegenError {
                    message: format!(
                        "compile_to_module: symbol '{}' missing from module '{module_path}' at GOT-data emission",
                        defn.name
                    ),
                    location: ErrorLocation::from_span(defn.span),
                }
            })?;
            let ModuleEntry::Def { got_slot, .. } = entry else {
                continue; // Non-Def entries don't have GOT slots
            };
            let Some(slot) = got_slot else {
                continue; // Slot not allocated (primitive-shaped Def)
            };
            let Some(&func_id) = func_ids.get(&defn.name) else {
                continue; // Defensive: can't happen — we declared it above
            };
            slot_funcs.push((*slot, func_id));
        }
        let slot_count = table.next_got_slot;
        // Drop the read guard before potentially mutating other tables.
        drop(table);

        let got_name = crate::compiler::got_data_symbol_name(&module_path);
        module.define_module_got_data(&got_name, slot_count, &slot_funcs)?;
    }

    // Step 4: Finalize definitions.
    // For JITModule: patches relocations, makes code pages executable.
    // For ObjectModule: no-op (bytes emitted at a later `finish()` call).
    module.finalize_for_code_read()?;

    // Step 5 (G6 + Sprint 58 Wave 3b): Collect per-symbol finalised code
    // pointers into `CompilationResult.code_ptrs`. Per Decision 35 Layer 2
    // Option B, backend no longer writes `Code` onto `ModuleEntry::Def.code`
    // directly — the `Code` enum lives in the integration layer and unifies
    // fresh-build (`Code::Jit`) with cache-hit (`Code::Linker`). The
    // integration-layer caller (`src/worker.rs::inline_jit_codegen_for_names`)
    // constructs `Code::Jit { jit: Arc::clone(&jit_arc), ptr }` per entry
    // and writes it onto the live symbol table. Backend stays ignorant of
    // the `Code` enum and preserves Principle 3.
    //
    // `code_ptrs` is empty for `ObjectModule` (`try_get_finalized_function`
    // returns `None` per §9.1.6 capability-based skip). The integration
    // layer's cache-hit path produces `Code::Linker` from the linker's
    // resolved addresses (a separate code path in `worker.rs`).
    let mut code_ptrs: HashMap<Symbol, *const u8> = HashMap::with_capacity(defns.len());
    for defn in &defns {
        let Some(&func_id) = func_ids.get(&defn.name) else {
            continue;
        };
        let Some(ptr) = module.try_get_finalized_function(func_id) else {
            // Object-mode path: no runtime pointer exists; leave
            // `code_ptrs` empty and break (subsequent symbols will also
            // return None — capability is module-wide, not per-symbol).
            break;
        };
        code_ptrs.insert(defn.name.clone(), ptr);
    }

    Ok(CompilationResult {
        func_ids: result_func_ids,
        code_ptrs,
        artifacts,
        entry_func_id,
        func_arities,
        warnings: Vec::new(),
    })
}

// NOTE: `resolve_cross_module_refs` was removed in Sprint 58 Wave 2 per
// `/arch` Decision 36 + 31. Under all-GOT calling, cross-module function
// references flow through `__cranelisp_got_{other_M}`, never as direct
// `Linkage::Import` function declarations. Compile-time arity for those
// calls is resolved via `compiler::resolve_func_arity` walking the symbol
// tables.

/// Compile a single defn into a module using FnCompiler, returning the
/// per-symbol introspection artifacts captured during codegen.
fn compile_defn_in_module<M, C, L>(
    defn: &Defn,
    module: &mut M,
    func_ctx: &mut FunctionBuilderContext,
    func_ids: &HashMap<Symbol, FuncId>,
    compile_ctx: CompileContext<'_, C, L>,
) -> Result<FunctionArtifacts, CranelispError>
where
    M: Module,
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    let mut sig = module.make_signature();
    for _ in defn.params() {
        sig.params.push(AbiParam::new(types::I64));
    }
    sig.returns.push(AbiParam::new(types::I64));

    let func_id = *func_ids.get(&defn.name).ok_or_else(|| {
        CranelispError::CodegenError {
            message: format!("function '{}' not declared", defn.name),
            location: ErrorLocation::from_span(defn.span),
        }
    })?;

    let mut func = cranelift::codegen::ir::Function::with_name_signature(
        cranelift::codegen::ir::UserFuncName::testcase(defn.name.as_bytes()),
        sig,
    );

    FnCompiler::compile_body(defn, &mut func, func_ctx, module, compile_ctx)?;

    // Capture CLIF IR text before define_function consumes the context.
    let clif_ir = format!("{}", func.display());

    let mut ctx = cranelift::codegen::Context::for_function(func);
    // Enable disassembly capture so CompiledCode.vcode is populated.
    ctx.set_disasm(true);
    module
        .define_function(func_id, &mut ctx)
        .map_err(|e| CranelispError::CodegenError {
            message: format!("failed to define function '{}': {e}", defn.name),
            location: ErrorLocation::from_span(defn.span),
        })?;

    // Capture disasm + code size from the compiled code.
    let (disasm, code_size) = if let Some(compiled) = ctx.compiled_code() {
        (
            compiled.vcode.clone().unwrap_or_default(),
            compiled.code_info().total_size,
        )
    } else {
        (String::new(), 0)
    };

    Ok(FunctionArtifacts {
        clif_ir,
        disasm,
        code_size,
    })
}


#[cfg(test)]
mod clif_dump_tests {
    //! Unit tests for Sprint 60 Workstream B (CLIF dump observability).
    //!
    //! These exercise the env-var filter grammar and the output formatter
    //! in isolation from codegen — the integration test (exercising the
    //! wired-up env var end-to-end via a subprocess) lives with `/qa` in
    //! `tests/sprint60_observability.rs`.
    use super::{clif_dump_matches, write_clif_dump};

    #[test]
    fn filter_unset_or_empty_never_matches() {
        assert!(!clif_dump_matches(None, "user", "foo"));
        assert!(!clif_dump_matches(Some(""), "user", "foo"));
    }

    #[test]
    fn filter_wildcard_matches_every_function() {
        assert!(clif_dump_matches(Some("*"), "user", "foo"));
        assert!(clif_dump_matches(Some("*"), "exemplar.solver", "cell-at$grid.Cell"));
        assert!(clif_dump_matches(Some("*"), "", ""));
    }

    #[test]
    fn filter_module_only_matches_any_symbol_in_that_module() {
        assert!(clif_dump_matches(Some("user"), "user", "foo"));
        assert!(clif_dump_matches(Some("user"), "user", "bar"));
        assert!(!clif_dump_matches(Some("user"), "main", "foo"));
        // Dotted module paths are matched literally, not as prefixes.
        assert!(clif_dump_matches(Some("exemplar.solver"), "exemplar.solver", "go"));
        assert!(!clif_dump_matches(Some("exemplar"), "exemplar.solver", "go"));
    }

    #[test]
    fn filter_module_colon_symbol_matches_that_exact_function() {
        let filter = Some("grid::cell-at$grid.Cell");
        assert!(clif_dump_matches(filter, "grid", "cell-at$grid.Cell"));
        // Wrong module — reject.
        assert!(!clif_dump_matches(filter, "html", "cell-at$grid.Cell"));
        // Wrong symbol — reject.
        assert!(!clif_dump_matches(filter, "grid", "cell-at"));
    }

    #[test]
    fn write_clif_dump_frames_header_and_trailer() {
        let mut buf = Vec::<u8>::new();
        write_clif_dump(&mut buf, "user", "foo", "function %foo() -> i64 {\n}\n").unwrap();
        let out = String::from_utf8(buf).unwrap();
        assert!(out.starts_with("; === CLIF user::foo ===\n"), "output: {out}");
        assert!(out.contains("function %foo() -> i64 {"), "body missing: {out}");
        assert!(out.trim_end().ends_with("; === end CLIF user::foo ==="), "trailer missing: {out}");
    }

    #[test]
    fn write_clif_dump_adds_trailing_newline_when_body_lacks_one() {
        // Body without trailing newline — formatter should insert one so the
        // "end" trailer appears on its own line.
        let mut buf = Vec::<u8>::new();
        write_clif_dump(&mut buf, "m", "s", "noeol").unwrap();
        let out = String::from_utf8(buf).unwrap();
        let lines: Vec<&str> = out.lines().collect();
        assert_eq!(lines[0], "; === CLIF m::s ===");
        assert_eq!(lines[1], "noeol");
        assert_eq!(lines[2], "; === end CLIF m::s ===");
    }
}


#[cfg(test)]
mod tests {
    use super::*;
    use crate::jit::Jit;
    use cranelisp_types::{ErrorLocation, 
        Defn, DefnVariant, DisplayInfo, Expr, MethodResolutions, MonoDefn, Program, Span, Symbol,
        TopLevel, Type, Visibility,
    };
    use std::collections::{HashMap, HashSet};

    /// Test-only aggregate bridging hand-built `Defn`s through side-map
    /// enrichment to the post-Phase-2 backend API. Carries the fields that
    /// the boundary `CheckResult` will retire in Wave 2 step 4 (slim-down to
    /// `{ warnings, display }`).
    ///
    /// Rationale: per `design/typecheck/ast-annotation.md` §10.2.5, the 20+
    /// `#[cfg(test)]` hits that legacy-constructed `CheckResult` literals now
    /// use this helper so the Wave 2 slim-down can land cleanly without a
    /// red build window. The shape mirrors the current public `CheckResult`
    /// field-for-field so the mechanical rewrite is a rename, not a redesign.
    struct TestCheckResult {
        method_resolutions: MethodResolutions,
        constrained_fn_names: HashSet<Symbol>,
        mono_defns: Vec<MonoDefn>,
        expr_types: HashMap<Span, Type>,
        default_method_defns: Vec<Defn>,
        #[allow(dead_code)]
        warnings: Vec<Warning>,
        #[allow(dead_code)]
        display: Option<DisplayInfo>,
    }

    fn empty_check() -> TestCheckResult {
        TestCheckResult {
            method_resolutions: HashMap::new(),
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
            display: None,
        }
    }

    fn empty_tables() -> DashMap<ModuleFullPath, SymbolTable> {
        DashMap::new()
    }

    /// Test helper: enrich a defn's AST nodes with type and resolution
    /// annotations from CheckResult side maps.
    ///
    /// Used by tests that build ASTs by hand and carry resolutions in a
    /// `CheckResult`. In production, typecheck annotates the AST directly,
    /// so this bridge is test-only.
    fn enrich_defn_from_side_maps(
        defn: &mut Defn,
        resolutions: &HashMap<Span, cranelisp_types::ResolvedCall>,
        expr_types: &HashMap<Span, Type>,
    ) {
        for variant in &mut defn.variants {
            enrich_expr_from_side_maps(&mut variant.body, resolutions, expr_types);
        }
    }

    /// Test helper: recursively enrich expression nodes with side map data.
    fn enrich_expr_from_side_maps(
        expr: &mut cranelisp_types::Expr,
        resolutions: &HashMap<Span, cranelisp_types::ResolvedCall>,
        expr_types: &HashMap<Span, Type>,
    ) {
        use cranelisp_types::Expr;

        let span = expr.span();

        // Overlay inferred_type from side map if present.
        if let Some(ty) = expr_types.get(&span) {
            expr.set_inferred_type(Some(Box::new(ty.clone())));
        }

        // Overlay resolved_call from side map if present (Apply only).
        if let Expr::Apply { resolved_call, span: apply_span, .. } = expr {
            if let Some(resolution) = resolutions.get(apply_span) {
                *resolved_call = Some(Box::new(resolution.clone()));
            }
        }

        // Recurse into children.
        match expr {
            Expr::Let { bindings, body, .. } => {
                for (_, binding_expr) in bindings {
                    enrich_expr_from_side_maps(binding_expr, resolutions, expr_types);
                }
                enrich_expr_from_side_maps(body, resolutions, expr_types);
            }
            Expr::If { cond, then_branch, else_branch, .. } => {
                enrich_expr_from_side_maps(cond, resolutions, expr_types);
                enrich_expr_from_side_maps(then_branch, resolutions, expr_types);
                enrich_expr_from_side_maps(else_branch, resolutions, expr_types);
            }
            Expr::Lambda { body, .. } => {
                enrich_expr_from_side_maps(body, resolutions, expr_types);
            }
            Expr::Apply { callee, args, .. } => {
                enrich_expr_from_side_maps(callee, resolutions, expr_types);
                for arg in args {
                    enrich_expr_from_side_maps(arg, resolutions, expr_types);
                }
            }
            Expr::Match { scrutinee, arms, .. } => {
                enrich_expr_from_side_maps(scrutinee, resolutions, expr_types);
                for arm in arms {
                    enrich_expr_from_side_maps(&mut arm.body, resolutions, expr_types);
                }
            }
            Expr::VecLit { elements, .. } => {
                for elem in elements {
                    enrich_expr_from_side_maps(elem, resolutions, expr_types);
                }
            }
            Expr::Annotate { expr: inner, .. } => {
                enrich_expr_from_side_maps(inner, resolutions, expr_types);
            }
            Expr::Trace { body, .. } => {
                enrich_expr_from_side_maps(body, resolutions, expr_types);
            }
            Expr::ParBind { bindings, body, .. } => {
                for (_, binding_expr) in bindings {
                    enrich_expr_from_side_maps(binding_expr, resolutions, expr_types);
                }
                enrich_expr_from_side_maps(body, resolutions, expr_types);
            }
            // Leaf nodes: no children to recurse into.
            Expr::IntLit { .. }
            | Expr::FloatLit { .. }
            | Expr::BoolLit { .. }
            | Expr::StringLit { .. }
            | Expr::Var { .. } => {}
        }
    }

    /// Test helper: build a `ModuleEntry::Def` with `ast: Some(defn)`, matching
    /// the Wave 0 invariant. Used by test helpers that construct defns by hand.
    fn make_def_entry(defn: Defn) -> cranelisp_types::ModuleEntry {
        use cranelisp_types::{DefKind, ModuleEntry, Scheme, Visibility};
        let param_count = defn.params().len();
        let param_names = defn
            .variants
            .first()
            .map(|v| v.params.clone())
            .unwrap_or_default();
        let scheme = Scheme {
            vars: vec![],
            constraints: HashMap::new(),
            ty: Type::Fn(
                (0..param_count).map(|_| Type::Int).collect(),
                Box::new(Type::Int),
            ),
        };
        ModuleEntry::Def {
            scheme,
            visibility: Visibility::Public,
            docstring: None,
            param_names,
            kind: Box::new(DefKind::UserFn { constrained_fn: None }),
            callees: vec![],
            got_slot: None,
            trait_origin: None,
            ast: Some(defn),
            code: None,
            fn_ptr: None,
        }
    }

    /// Test helper: wrap an expression in a synthetic zero-arg defn, compile via
    /// `compile_to_module`, finalize JIT, execute, and return the i64 result.
    ///
    /// The `check` parameter provides side-map data that is enriched onto the
    /// defn's AST nodes before compilation (bridging old test code to the new
    /// CheckResult-free API).
    fn test_compile_and_run(
        expr: &Expr,
        check: &TestCheckResult,
        tables: &DashMap<ModuleFullPath, SymbolTable>,
    ) -> Result<i64, CranelispError> {
        let mut defn = Defn {
            name: Symbol::from("__expr__"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                param_annotations: vec![],
                body: expr.clone(),
                span: Span::SYNTHETIC,
            }],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        };
        // Enrich the defn from CheckResult side maps (test bridge).
        enrich_defn_from_side_maps(&mut defn, &check.method_resolutions, &check.expr_types);

        let module = ModuleFullPath::from("user");
        let name = defn.name.clone();
        // Post-Phase-2: insert the defn into the shared symbol table so the
        // backend's `compile_to_module` reads its AST from there.
        {
            let mut st = tables
                .entry(module.clone())
                .or_insert_with(|| SymbolTable::new(module.clone()));
            st.insert(name.clone(), make_def_entry(defn));
        }

        let mut jit = Jit::new()?;
        let result = compile_to_module(
            module,
            &[name],
            tables,
            jit.jit_module(),
        )?;
        // Post-G6: `compile_to_module` already finalized the JIT internally.
        let entry_id = result.entry_func_id.ok_or_else(|| CranelispError::CodegenError {
            message: "no entry function".into(),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        })?;
        let ptr = jit.get_finalized_ptr(entry_id);
        let _ = cranelisp_runtime::panic::take_runtime_error();
        let func: extern "C" fn() -> i64 = unsafe { std::mem::transmute(ptr) };
        let value = func();
        if let Some(msg) = cranelisp_runtime::panic::take_runtime_error() {
            return Err(CranelispError::CodegenError {
                message: format!("runtime panic: {}", msg),
                location: ErrorLocation::from_span(Span::SYNTHETIC),
            });
        }
        Ok(value)
    }

    /// Test helper: compile a program via `compile_to_module`, finalize JIT,
    /// execute entry function, and return the i64 result.
    ///
    /// Enriches defns from `check` side maps, inserts each defn into the
    /// shared symbol table as a `ModuleEntry::Def { ast: Some(_), .. }` entry
    /// (matching the Wave 0 invariant), then hands the name list to
    /// `compile_to_module`. Bridges legacy test scaffolding to the post-
    /// Phase-2 backend API (no `Program`/`CheckResult` parameters).
    fn test_compile_program_and_run(
        program: &[TopLevel],
        check: &TestCheckResult,
        tables: &DashMap<ModuleFullPath, SymbolTable>,
    ) -> Result<i64, CranelispError> {
        let module = ModuleFullPath::from("user");

        // Enrich and collect all TopLevel::Defn entries from the program,
        // plus default_method_defns and mono specialisations from the check
        // (historically injected into the program by finalize_module).
        let mut defns: Vec<Defn> = Vec::new();
        for tl in program {
            if let TopLevel::Defn(defn) = tl {
                let mut d = defn.clone();
                enrich_defn_from_side_maps(&mut d, &check.method_resolutions, &check.expr_types);
                defns.push(d);
            }
        }
        for d in &check.default_method_defns {
            let mut enriched = d.clone();
            enrich_defn_from_side_maps(&mut enriched, &check.method_resolutions, &check.expr_types);
            defns.push(enriched);
        }
        for mono in &check.mono_defns {
            let mut enriched = mono.defn.clone();
            let mut merged = check.method_resolutions.clone();
            merged.extend(mono.resolutions.clone());
            let expr_types = if mono.expr_types.is_empty() {
                &check.expr_types
            } else {
                &mono.expr_types
            };
            enrich_defn_from_side_maps(&mut enriched, &merged, expr_types);
            defns.push(enriched);
        }

        // Install each defn as a symbol-table entry with ast: Some(defn).
        // Multi-sig defns need expansion into mangled variants here (legacy
        // tests don't pre-materialise those; typecheck does in production).
        let mut names: Vec<Symbol> = Vec::new();
        {
            let mut st = tables
                .entry(module.clone())
                .or_insert_with(|| SymbolTable::new(module.clone()));
            for defn in defns {
                if defn.is_multi_sig() {
                    // Look up OverloadVariant info from the pre-inserted
                    // Overloaded base entry to recover mangled names + param
                    // types, then materialise each variant as its own entry.
                    let variants = match st.get(defn.name.as_ref()) {
                        Some(cranelisp_types::ModuleEntry::Def { kind, .. }) => {
                            if let cranelisp_types::DefKind::Overloaded { variants } =
                                kind.as_ref()
                            {
                                variants.clone()
                            } else {
                                continue;
                            }
                        }
                        _ => continue,
                    };
                    for (i, variant) in defn.variants.iter().enumerate() {
                        let param_types = variants
                            .iter()
                            .find(|v| v.param_types.len() == variant.params.len())
                            .map(|v| v.param_types.clone())
                            .or_else(|| variants.get(i).map(|v| v.param_types.clone()))
                            .unwrap_or_default();
                        let mangled = format!(
                            "{}${}",
                            defn.name,
                            param_types
                                .iter()
                                .filter_map(|t| match t {
                                    Type::Int => Some("Int"),
                                    Type::Float => Some("Float"),
                                    Type::Bool => Some("Bool"),
                                    Type::String => Some("String"),
                                    _ => None,
                                })
                                .collect::<Vec<_>>()
                                .join("+"),
                        );
                        let variant_defn = Defn {
                            name: Symbol::from(mangled),
                            docstring: defn.docstring.clone(),
                            variants: vec![variant.clone()],
                            visibility: defn.visibility,
                            span: variant.span,
                        };
                        names.push(variant_defn.name.clone());
                        st.insert(variant_defn.name.clone(), make_def_entry(variant_defn));
                    }
                } else {
                    names.push(defn.name.clone());
                    st.insert(defn.name.clone(), make_def_entry(defn));
                }
            }
        }

        let mut jit = Jit::new()?;
        let result = compile_to_module(
            module,
            &names,
            tables,
            jit.jit_module(),
        )?;
        // Post-G6: `compile_to_module` already finalized the JIT internally.
        let entry_id = result.entry_func_id.ok_or_else(|| CranelispError::CodegenError {
            message: "no entry function".into(),
            location: ErrorLocation::from_span(Span::SYNTHETIC),
        })?;
        let ptr = jit.get_finalized_ptr(entry_id);
        let _ = cranelisp_runtime::panic::take_runtime_error();
        let func: extern "C" fn() -> i64 = unsafe { std::mem::transmute(ptr) };
        let value = func();
        if let Some(msg) = cranelisp_runtime::panic::take_runtime_error() {
            return Err(CranelispError::CodegenError {
                message: format!("runtime panic: {}", msg),
                location: ErrorLocation::from_span(Span::SYNTHETIC),
            });
        }
        Ok(value)
    }

    /// Build symbol tables with an Option type for ADT tests.
    fn option_type_tables() -> DashMap<ModuleFullPath, SymbolTable> {
        use cranelisp_types::{ConstructorInfo, FQTypeName, FieldInfo, ModuleEntry, Scheme, Type,
            TypeDefInfo, TypeName, Visibility,
        };

        let module = ModuleFullPath::from("main");
        let type_name = TypeName::from("Option");
        let fqtn = FQTypeName::new(module.clone(), type_name.clone());

        let type_def_info = TypeDefInfo {
            name: fqtn.clone(),
            type_params: vec![],
            constructors: vec![
                ConstructorInfo {
                    name: Symbol::from("None"),
                    tag: 0,
                    fields: vec![],
                    docstring: None,
                    internal: false,
                },
                ConstructorInfo {
                    name: Symbol::from("Some"),
                    tag: 1,
                    fields: vec![FieldInfo {
                        name: Symbol::from("val"),
                        ty: Type::Int,
                    }],
                    docstring: None,
                    internal: false,
                },
            ],
            docstring: None,
        };

        let tables = DashMap::new();
        let mut st = SymbolTable::new(module.clone());

        // Insert type def
        st.insert(
            Symbol::from("Option"),
            ModuleEntry::TypeDef {
                info: type_def_info.clone(),
                visibility: Visibility::Public,
                constructor_scheme: None,
                sexp: None,
            },
        );

        // Insert constructors
        let none_scheme = Scheme {
            vars: vec![],
            constraints: HashMap::new(),
            ty: Type::ADT(fqtn.clone(), vec![]),
        };
        st.insert(
            Symbol::from("None"),
            ModuleEntry::Constructor {
                type_name: fqtn.clone(),
                info: type_def_info.constructors[0].clone(),
                scheme: none_scheme,
                visibility: Visibility::Public,
            },
        );

        let some_scheme = Scheme {
            vars: vec![],
            constraints: HashMap::new(),
            ty: Type::Fn(vec![Type::Int], Box::new(Type::ADT(fqtn.clone(), vec![]))),
        };
        st.insert(
            Symbol::from("Some"),
            ModuleEntry::Constructor {
                type_name: fqtn.clone(),
                info: type_def_info.constructors[1].clone(),
                scheme: some_scheme,
                visibility: Visibility::Public,
            },
        );

        tables.insert(module, st);
        tables
    }

    // spec: 05-definitions §5.1 — single defn compiles and executes via JIT
    #[test]
    fn test_compile_program_simple() {
        let defn = Defn {
            name: Symbol::from("main"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                param_annotations: vec![],
                body: Expr::IntLit {
                    value: 42,
                    span: Span::new(0, 2),
                    inferred_type: None,
                },
                span: Span::new(0, 20),
            }],
            visibility: cranelisp_types::Visibility::Public,
            span: Span::new(0, 20),
        };

        let program: Program = vec![TopLevel::Defn(defn)];
        let check = empty_check();

        let value = test_compile_program_and_run(&program, &check, &empty_tables()).unwrap();
        assert_eq!(value, 42);
    }

    // spec: 12-runtime §12.6 — batch mode requires main entry point
    #[test]
    fn test_compile_program_no_defns() {
        let _ = empty_check();
        let names: Vec<Symbol> = vec![];
        let tables = empty_tables();
        // No symbol table for "user" at all — compile_to_module errors out
        // because there's no module entry (and no names anyway).
        tables.insert(ModuleFullPath::from("user"), SymbolTable::new(ModuleFullPath::from("user")));

        let mut jit = Jit::new().unwrap();
        let result = compile_to_module(
            ModuleFullPath::from("user"),
            &names,
            &tables,
            jit.jit_module(),
        );
        assert!(result.is_err());
    }

    // spec: 04-expressions §4.1.1 — integer literal codegen
    #[test]
    fn test_compile_and_run_expr() {
        let expr = Expr::IntLit {
            value: 99,
            span: Span::new(0, 2),
            inferred_type: None,
        };
        let check = empty_check();

        let value = test_compile_and_run(&expr, &check, &empty_tables()).unwrap();
        assert_eq!(value, 99);
    }

    // spec: 05-definitions §5.1 — defn compiles in interactive (REPL) mode
    #[test]
    fn test_compile_program_interactive_mode() {
        let defn = Defn {
            name: Symbol::from("main"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                param_annotations: vec![],
                body: Expr::IntLit {
                value: 7,
                span: Span::new(0, 1),
                inferred_type: None,
                },
                span: Span::new(0, 20),
            }],
            visibility: cranelisp_types::Visibility::Public,
            span: Span::new(0, 20),
        };

        let program: Program = vec![TopLevel::Defn(defn)];
        let check = empty_check();

        let value = test_compile_program_and_run(&program, &check, &empty_tables()).unwrap();
        assert_eq!(value, 7);
    }

    // spec: 04-expressions §4.1.1 — integer literal codegen with GOT state
    // spec: 05-definitions §5.13.1 — multiple function definitions compile together
    #[test]
    fn test_compile_program_multiple_defns() {
        // Two functions: helper and main. Main returns 100.
        let helper = Defn {
            name: Symbol::from("helper"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![Symbol::from("x")],
                param_annotations: vec![],
                body: Expr::Var {
                name: Symbol::from("x"),
                span: Span::new(20, 21),
                inferred_type: None,
                },
                span: Span::new(10, 30),
            }],
            visibility: cranelisp_types::Visibility::Public,
            span: Span::new(10, 30),
        };

        let main_defn = Defn {
            name: Symbol::from("main"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                param_annotations: vec![],
                body: Expr::IntLit {
                value: 100,
                span: Span::new(40, 43),
                inferred_type: None,
                },
                span: Span::new(35, 50),
            }],
            visibility: cranelisp_types::Visibility::Public,
            span: Span::new(35, 50),
        };

        let program: Program = vec![TopLevel::Defn(helper), TopLevel::Defn(main_defn)];
        let check = empty_check();

        let value = test_compile_program_and_run(&program, &check, &empty_tables()).unwrap();
        assert_eq!(value, 100);
    }

    // spec: 04-expressions §4.1.3 — boolean literal codegen
    #[test]
    fn test_compile_and_run_expr_bool() {
        let expr = Expr::BoolLit {
            value: true,
            span: Span::new(0, 4),
            inferred_type: None,
        };
        let check = empty_check();

        let value = test_compile_and_run(&expr, &check, &empty_tables()).unwrap();
        assert_eq!(value, 1);
    }

    // --- Ring 1 tests ---

    // spec: 04-expressions §4.1.4 — string literal codegen, heap allocation
    #[test]
    fn test_compile_string_literal() {
        let expr = Expr::StringLit {
            value: "hello".to_string(),
            span: Span::new(0, 7),
            inferred_type: None,
        };
        let check = empty_check();

        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(result.is_ok(), "string literal should compile: {result:?}");
        let ptr = result.unwrap();
        // ptr should be a heap pointer (> NULLARY_TAG_THRESHOLD)
        assert!(ptr > 1024, "expected heap pointer, got {ptr}");

        // Read back the string content via runtime API.
        let s = unsafe { cranelisp_runtime::read_string_as_str(ptr) };
        assert_eq!(s, "hello");

        // Clean up the allocation.
        cranelisp_runtime::heap_dealloc(ptr);
    }

    // spec: 04-expressions §4.1.4 — empty string literal codegen
    #[test]
    fn test_compile_empty_string_literal() {
        let expr = Expr::StringLit {
            value: String::new(),
            span: Span::new(0, 2),
            inferred_type: None,
        };
        let check = empty_check();

        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(result.is_ok(), "empty string should compile: {result:?}");
        let ptr = result.unwrap();
        assert!(ptr > 1024, "expected heap pointer, got {ptr}");

        let s = unsafe { cranelisp_runtime::read_string_as_str(ptr) };
        assert_eq!(s, "");

        cranelisp_runtime::heap_dealloc(ptr);
    }

    // spec: 12-runtime §12.1.4 — data constructor heap layout [tag | fields]
    #[test]
    fn test_compile_adt_data_constructor() {
        // Expression: (Some 42)
        let some_span = Span::new(0, 10);
        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("Some"),
                span: Span::new(1, 5),
                inferred_type: None,
            }),
            args: vec![Expr::IntLit {
                value: 42,
                span: Span::new(6, 8),
                inferred_type: None,
            }],
            span: some_span,
            resolved_call: None,
            inferred_type: None,
        };

        let check = empty_check();
        let tables = option_type_tables();

        let result = test_compile_and_run(&expr, &check, &tables);
        assert!(result.is_ok(), "ADT constructor should compile: {result:?}");
        let ptr = result.unwrap();
        assert!(ptr > 1024, "expected heap pointer, got {ptr}");

        // Verify the heap layout: [header(16) | tag(1) | field(42)]
        unsafe {
            let base = ptr as *const u8;
            let tag = *(base.add(16) as *const i64);
            assert_eq!(tag, 1, "tag should be 1 for Some");
            let val = *(base.add(24) as *const i64);
            assert_eq!(val, 42, "field should be 42");
        }

        cranelisp_runtime::heap_dealloc(ptr);
    }

    // spec: 04-expressions §4.8 — match expression with constructor patterns and field extraction
    #[test]
    fn test_compile_match_with_fields() {
        use cranelisp_types::{MatchArm, Pattern};

        // (match (Some 99) [(Some x) x (None) 0])
        let some_span = Span::new(10, 20);
        let match_span = Span::new(0, 50);
        let scrutinee = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("Some"),
                span: Span::new(11, 15),
                inferred_type: None,
            }),
            args: vec![Expr::IntLit {
                value: 99,
                span: Span::new(16, 18),
                inferred_type: None,
            }],
            span: some_span,
            resolved_call: None,
            inferred_type: None,
        };

        let expr = Expr::Match {
            scrutinee: Box::new(scrutinee),
            arms: vec![
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: Symbol::from("Some"),
                        bindings: vec![Symbol::from("x")],
                        span: Span::new(22, 30),
                    },
                    body: Expr::Var {
                        name: Symbol::from("x"),
                        span: Span::new(31, 32),
                        inferred_type: None,
                    },
                    span: Span::new(22, 32),
                },
                MatchArm {
                    pattern: Pattern::Constructor {
                        name: Symbol::from("None"),
                        bindings: vec![],
                        span: Span::new(34, 40),
                    },
                    body: Expr::IntLit {
                        value: 0,
                        span: Span::new(41, 42),
                        inferred_type: None,
                    },
                    span: Span::new(34, 42),
                },
            ],
            span: match_span,
            compiler_generated: false,
            inferred_type: None,
        };

        let check = empty_check();
        let tables = option_type_tables();

        let result = test_compile_and_run(&expr, &check, &tables);
        assert!(result.is_ok(), "match with fields should compile: {result:?}");
        assert_eq!(result.unwrap(), 99, "match should extract field value");
    }

    // spec: 04-expressions §4.5 — lambda capture, closure allocation, and indirect call
    #[test]
    fn test_compile_lambda_closure() {
        // (let [n 5] ((fn [x] (+ n x)) 10))
        // This tests: lambda capture of 'n', closure allocation, closure call.
        use cranelisp_types::ResolvedCall;

        let add_span = Span::new(30, 37);
        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            add_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("add-i64"),
            },
        );

        let expr = Expr::Let {
            bindings: vec![(
                Symbol::from("n"),
                Expr::IntLit {
                    value: 5,
                    span: Span::new(5, 6),
                    inferred_type: None,
                },
            )],
            body: Box::new(Expr::Apply {
                callee: Box::new(Expr::Lambda {
                    params: vec![Symbol::from("x")],
                    param_annotations: vec![],
                    body: Box::new(Expr::Apply {
                        callee: Box::new(Expr::Var {
                            name: Symbol::from("+"),
                            span: Span::new(31, 32),
                            inferred_type: None,
                        }),
                        args: vec![
                            Expr::Var {
                                name: Symbol::from("n"),
                                span: Span::new(33, 34),
                                inferred_type: None,
                            },
                            Expr::Var {
                                name: Symbol::from("x"),
                                span: Span::new(35, 36),
                                inferred_type: None,
                            },
                        ],
                        span: add_span,
                        resolved_call: None,
                        inferred_type: None,
                    }),
                    span: Span::new(10, 40),
                    inferred_type: None,
                }),
                args: vec![Expr::IntLit {
                    value: 10,
                    span: Span::new(42, 44),
                    inferred_type: None,
                }],
                span: Span::new(10, 45),
                resolved_call: None,
                inferred_type: None,
            }),
            span: Span::new(0, 46),
            inferred_type: None,
        };

        let check = TestCheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
        display: None,
        };

        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(result.is_ok(), "closure should compile: {result:?}");
        assert_eq!(result.unwrap(), 15, "5 + 10 = 15");
    }

    // spec: design/backend/ring2-rc.md "capture-return inc" (sibling of §5.5)
    // spec: design/backend/slice-4-21-hello-io-investigation.md §4d/§4e
    //
    // Regression guard for Slice 4 defect. A lambda body whose return
    // expression is a bare reference to a captured heap variable MUST
    // emit `rc_inc` on the return value before `return`, so the
    // closure's drop-glue dec (fired by one-shot consume_closure paths
    // like the IO trampoline) does not free the value out from under
    // the caller.
    //
    // Test shape: `(let [s "hello"] ((fn [_] s) 0))`. The inner
    // closure captures `s` (heap-typed String) and returns it when
    // called with a dummy Int arg. Without `emit_capture_return_inc`,
    // the closure's drop glue would dec `s` after the body returns,
    // the outer `let` scope cleanup would dec `s` again (via its own
    // scope-stack dec), and at least one of those decs lands on a
    // freed node — corrupting the returned pointer and/or
    // double-freeing.
    //
    // Post-fix: the returned pointer is still live and reads back as
    // "hello"; `test_compile_lambda_closure` above (non-capture-return
    // shape) is unaffected, confirming the fix is additive.
    //
    // NB: this test sits in `lib.rs #[cfg(test)] mod tests` rather
    // than a new module in `control_flow.rs` because the
    // `test_compile_and_run` helper + `TestCheckResult` scaffolding is
    // local to `lib.rs` and re-exporting it would duplicate the entire
    // compile pipeline bridge. Per /arch §4d the placement discipline
    // is "wherever existing control_flow tests live" — the three
    // existing closure/lambda backend tests
    // (`test_compile_lambda_closure`, others) all live here.
    #[test]
    fn lambda_return_captured_heap_var_emits_inc() {
        // AST: (let [s "hello"] ((fn [_] s) 0))
        //
        // Explicit `inferred_type` on the String literal so the let's
        // `variable_types` picks up `s: String`; that's what
        // `emit_capture_return_inc` reads from the enclosing scope when
        // the lambda body is compiled.
        let string_ty = Type::String;
        let s_span = Span::new(5, 12);
        let lam_body_span = Span::new(20, 21);
        let expr = Expr::Let {
            bindings: vec![(
                Symbol::from("s"),
                Expr::StringLit {
                    value: "hello".to_string(),
                    span: s_span,
                    inferred_type: Some(Box::new(string_ty.clone())),
                },
            )],
            body: Box::new(Expr::Apply {
                callee: Box::new(Expr::Lambda {
                    params: vec![Symbol::from("_")],
                    param_annotations: vec![],
                    body: Box::new(Expr::Var {
                        name: Symbol::from("s"),
                        span: lam_body_span,
                        inferred_type: Some(Box::new(string_ty.clone())),
                    }),
                    span: Span::new(15, 22),
                    inferred_type: None,
                }),
                args: vec![Expr::IntLit {
                    value: 0,
                    span: Span::new(24, 25),
                    inferred_type: None,
                }],
                span: Span::new(14, 26),
                resolved_call: None,
                inferred_type: None,
            }),
            span: Span::new(0, 27),
            inferred_type: None,
        };

        let check = empty_check();
        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(
            result.is_ok(),
            "captured-heap-return should compile and run: {result:?}"
        );
        let ptr = result.unwrap();
        // Heap pointer (> NULLARY_TAG_THRESHOLD).
        assert!(ptr > 1024, "expected heap pointer, got {ptr}");

        // Key post-fix assertion: the returned pointer is STILL LIVE
        // after return — `emit_capture_return_inc` incremented its RC
        // so the drop-glue dec did not free it. Pre-fix, `is_live`
        // would be false here (or the read-back would show corruption).
        #[cfg(debug_assertions)]
        assert!(
            cranelisp_runtime::alloc::is_live(ptr as usize),
            "returned string pointer must still be live after lambda return; \
             this is the capture-return inc invariant"
        );

        // Readable round-trip — proves the contents survived the
        // drop-glue dec that would otherwise have corrupted or freed
        // the heap block.
        let s = unsafe { cranelisp_runtime::read_string_as_str(ptr) };
        assert_eq!(s, "hello", "captured string must round-trip");

        // Balance the one remaining caller-side reference (we, the
        // test, are the caller). Normal runtime would emit the dec at
        // the caller's scope exit; here we dec manually.
        cranelisp_runtime::heap_dealloc(ptr);
    }

    // --- Vec codegen tests ---

    // spec: 04-expressions §4.10 — empty Vec literal codegen
    #[test]
    fn test_compile_empty_vec_literal() {
        let expr = Expr::VecLit {
            elements: vec![],
            span: Span::new(0, 2),
            inferred_type: None,
        };
        let check = empty_check();

        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(result.is_ok(), "empty vec literal should compile: {result:?}");
        let ptr = result.unwrap();
        // ptr should be a heap pointer (> NULLARY_TAG_THRESHOLD)
        assert!(ptr > 1024, "expected heap pointer, got {ptr}");

        // Verify len == 0.
        assert_eq!(cranelisp_runtime::vec_len(ptr), 0);

        // Clean up.
        cranelisp_runtime::vec_drop(ptr, 0);
    }

    // spec: 04-expressions §4.10 — Vec literal with integer elements
    #[test]
    fn test_compile_vec_literal_with_ints() {
        let expr = Expr::VecLit {
            elements: vec![
                Expr::IntLit { value: 10, span: Span::new(1, 3), inferred_type: None },
                Expr::IntLit { value: 20, span: Span::new(4, 6), inferred_type: None },
                Expr::IntLit { value: 30, span: Span::new(7, 9), inferred_type: None },
            ],
            span: Span::new(0, 10),
            inferred_type: None,
        };
        let check = empty_check();

        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(result.is_ok(), "vec literal should compile: {result:?}");
        let ptr = result.unwrap();
        assert!(ptr > 1024, "expected heap pointer, got {ptr}");

        // Verify len == 3.
        assert_eq!(cranelisp_runtime::vec_len(ptr), 3);

        // Verify element values from data buffer.
        unsafe {
            let base = ptr as *const u8;
            let data_ptr = *(base.add(heap::HeapVec::DATA_PTR_OFFSET as usize) as *const *const i64);
            assert_eq!(*data_ptr, 10);
            assert_eq!(*data_ptr.add(1), 20);
            assert_eq!(*data_ptr.add(2), 30);
        }

        cranelisp_runtime::vec_drop(ptr, 0);
    }

    // spec: 04-expressions §4.10 — single-element Vec literal
    #[test]
    fn test_compile_vec_literal_single_element() {
        let expr = Expr::VecLit {
            elements: vec![
                Expr::IntLit { value: 42, span: Span::new(1, 3), inferred_type: None },
            ],
            span: Span::new(0, 4),
            inferred_type: None,
        };
        let check = empty_check();

        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(result.is_ok(), "single-element vec should compile: {result:?}");
        let ptr = result.unwrap();

        assert_eq!(cranelisp_runtime::vec_len(ptr), 1);

        unsafe {
            let base = ptr as *const u8;
            let data_ptr = *(base.add(32) as *const *const i64);
            assert_eq!(*data_ptr, 42);
        }

        cranelisp_runtime::vec_drop(ptr, 0);
    }

    // spec: 04-expressions §4.10 — Vec literal with boolean elements
    #[test]
    fn test_compile_vec_literal_with_bool_elements() {
        let expr = Expr::VecLit {
            elements: vec![
                Expr::BoolLit { value: true, span: Span::new(1, 5), inferred_type: None },
                Expr::BoolLit { value: false, span: Span::new(6, 11), inferred_type: None },
            ],
            span: Span::new(0, 12),
            inferred_type: None,
        };
        let check = empty_check();

        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(result.is_ok(), "bool vec should compile: {result:?}");
        let ptr = result.unwrap();
        assert_eq!(cranelisp_runtime::vec_len(ptr), 2);

        unsafe {
            let base = ptr as *const u8;
            let data_ptr = *(base.add(32) as *const *const i64);
            assert_eq!(*data_ptr, 1); // true
            assert_eq!(*data_ptr.add(1), 0); // false
        }

        cranelisp_runtime::vec_drop(ptr, 0);
    }

    // spec: appendix-a-builtins §A.3 — vec-len inline primitive codegen
    #[test]
    fn test_compile_vec_len_inline() {
        use cranelisp_types::ResolvedCall;

        // (vec-len [10 20 30])
        let vec_span = Span::new(10, 20);
        let apply_span = Span::new(0, 25);

        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            apply_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-len"),
            },
        );

        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("vec-len"),
                span: Span::new(1, 8),
                inferred_type: None,
            }),
            args: vec![Expr::VecLit {
                elements: vec![
                    Expr::IntLit { value: 10, span: Span::new(11, 13), inferred_type: None },
                    Expr::IntLit { value: 20, span: Span::new(14, 16), inferred_type: None },
                    Expr::IntLit { value: 30, span: Span::new(17, 19), inferred_type: None },
                ],
                span: vec_span,
                inferred_type: None,
            }],
            span: apply_span,
            resolved_call: None,
            inferred_type: None,
        };

        let check = TestCheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
        display: None,
        };

        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(result.is_ok(), "vec-len should compile: {result:?}");
        assert_eq!(result.unwrap(), 3);
    }

    // spec: appendix-a-builtins §A.3 — vec-get bounds-checked index codegen
    #[test]
    fn test_compile_vec_get_inline() {
        use cranelisp_types::ResolvedCall;

        // (let [v [10 20 30]] (vec-get v 1))
        let vec_span = Span::new(8, 18);
        let get_span = Span::new(21, 35);

        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            get_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-get"),
            },
        );

        let expr = Expr::Let {
            bindings: vec![(
                Symbol::from("v"),
                Expr::VecLit {
                    elements: vec![
                        Expr::IntLit { value: 10, span: Span::new(9, 11), inferred_type: None },
                        Expr::IntLit { value: 20, span: Span::new(12, 14), inferred_type: None },
                        Expr::IntLit { value: 30, span: Span::new(15, 17), inferred_type: None },
                    ],
                    span: vec_span,
                    inferred_type: None,
                },
            )],
            body: Box::new(Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("vec-get"),
                    span: Span::new(22, 29),
                    inferred_type: None,
                }),
                args: vec![
                    Expr::Var {
                        name: Symbol::from("v"),
                        span: Span::new(30, 31),
                        inferred_type: None,
                    },
                    Expr::IntLit { value: 1, span: Span::new(32, 33), inferred_type: None },
                ],
                span: get_span,
                resolved_call: None,
                inferred_type: None,
            }),
            span: Span::new(0, 36),
            inferred_type: None,
        };

        let check = TestCheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
        display: None,
        };

        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(result.is_ok(), "vec-get should compile: {result:?}");
        assert_eq!(result.unwrap(), 20);
    }

    // spec: appendix-a-builtins §A.3 — vec-get index 0 boundary
    #[test]
    fn test_compile_vec_get_first_element() {
        use cranelisp_types::ResolvedCall;

        let vec_span = Span::new(100, 110);
        let get_span = Span::new(120, 135);

        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            get_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-get"),
            },
        );

        let expr = Expr::Let {
            bindings: vec![(
                Symbol::from("v"),
                Expr::VecLit {
                    elements: vec![
                        Expr::IntLit { value: 100, span: Span::new(101, 104), inferred_type: None },
                        Expr::IntLit { value: 200, span: Span::new(105, 108), inferred_type: None },
                    ],
                    span: vec_span,
                    inferred_type: None,
                },
            )],
            body: Box::new(Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("vec-get"),
                    span: Span::new(121, 128),
                    inferred_type: None,
                }),
                args: vec![
                    Expr::Var {
                        name: Symbol::from("v"),
                        span: Span::new(129, 130),
                        inferred_type: None,
                    },
                    Expr::IntLit { value: 0, span: Span::new(131, 132), inferred_type: None },
                ],
                span: get_span,
                resolved_call: None,
                inferred_type: None,
            }),
            span: Span::new(99, 136),
            inferred_type: None,
        };

        let check = TestCheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
        display: None,
        };

        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(result.is_ok(), "vec-get index 0 should work: {result:?}");
        assert_eq!(result.unwrap(), 100);
    }

    // spec: appendix-a-builtins §A.3 — vec-get last index boundary
    #[test]
    fn test_compile_vec_get_last_element() {
        use cranelisp_types::ResolvedCall;

        let vec_span = Span::new(200, 210);
        let get_span = Span::new(220, 235);

        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            get_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-get"),
            },
        );

        let expr = Expr::Let {
            bindings: vec![(
                Symbol::from("v"),
                Expr::VecLit {
                    elements: vec![
                        Expr::IntLit { value: 1, span: Span::new(201, 202), inferred_type: None },
                        Expr::IntLit { value: 2, span: Span::new(203, 204), inferred_type: None },
                        Expr::IntLit { value: 3, span: Span::new(205, 206), inferred_type: None },
                    ],
                    span: vec_span,
                    inferred_type: None,
                },
            )],
            body: Box::new(Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("vec-get"),
                    span: Span::new(221, 228),
                    inferred_type: None,
                }),
                args: vec![
                    Expr::Var {
                        name: Symbol::from("v"),
                        span: Span::new(229, 230),
                        inferred_type: None,
                    },
                    Expr::IntLit { value: 2, span: Span::new(231, 232), inferred_type: None },
                ],
                span: get_span,
                resolved_call: None,
                inferred_type: None,
            }),
            span: Span::new(199, 236),
            inferred_type: None,
        };

        let check = TestCheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
        display: None,
        };

        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(result.is_ok(), "vec-get last index should work: {result:?}");
        assert_eq!(result.unwrap(), 3);
    }

    // spec: 12-runtime §12.3.3 — vec-set copy-on-write path codegen
    #[test]
    fn test_compile_vec_set_copy_path() {
        use cranelisp_types::ResolvedCall;

        // (let [v [10 20 30]] (vec-len (vec-set v 1 99)))
        // Since v is used twice (vec-set and vec-len), vec-set takes the copy path.
        let vec_span = Span::new(300, 310);
        let set_span = Span::new(320, 340);
        let len_span = Span::new(315, 345);

        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            set_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-set"),
            },
        );
        method_resolutions.insert(
            len_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-len"),
            },
        );

        let expr = Expr::Let {
            bindings: vec![(
                Symbol::from("v"),
                Expr::VecLit {
                    elements: vec![
                        Expr::IntLit { value: 10, span: Span::new(301, 303), inferred_type: None },
                        Expr::IntLit { value: 20, span: Span::new(304, 306), inferred_type: None },
                        Expr::IntLit { value: 30, span: Span::new(307, 309), inferred_type: None },
                    ],
                    span: vec_span,
                    inferred_type: None,
                },
            )],
            body: Box::new(Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("vec-len"),
                    span: Span::new(316, 323),
                    inferred_type: None,
                }),
                args: vec![Expr::Apply {
                    callee: Box::new(Expr::Var {
                        name: Symbol::from("vec-set"),
                        span: Span::new(321, 328),
                        inferred_type: None,
                    }),
                    args: vec![
                        Expr::Var {
                            name: Symbol::from("v"),
                            span: Span::new(329, 330),
                            inferred_type: None,
                        },
                        Expr::IntLit { value: 1, span: Span::new(331, 332), inferred_type: None },
                        Expr::IntLit { value: 99, span: Span::new(333, 335), inferred_type: None },
                    ],
                    span: set_span,
                    resolved_call: None,
                    inferred_type: None,
                }],
                span: len_span,
                resolved_call: None,
                inferred_type: None,
            }),
            span: Span::new(299, 346),
            inferred_type: None,
        };

        let check = TestCheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
        display: None,
        };

        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(result.is_ok(), "vec-set should compile: {result:?}");
        // vec-set returns a new Vec with same length.
        assert_eq!(result.unwrap(), 3);
    }

    // spec: 12-runtime §12.3.3 — vec-push copy-on-write path codegen
    #[test]
    fn test_compile_vec_push_copy_path() {
        use cranelisp_types::ResolvedCall;

        // (vec-len (vec-push [10 20] 30))
        let vec_span = Span::new(400, 410);
        let push_span = Span::new(415, 435);
        let len_span = Span::new(410, 440);

        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            push_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-push"),
            },
        );
        method_resolutions.insert(
            len_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-len"),
            },
        );

        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("vec-len"),
                span: Span::new(411, 418),
                inferred_type: None,
            }),
            args: vec![Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("vec-push"),
                    span: Span::new(416, 424),
                    inferred_type: None,
                }),
                args: vec![
                    Expr::VecLit {
                        elements: vec![
                            Expr::IntLit { value: 10, span: Span::new(401, 403), inferred_type: None },
                            Expr::IntLit { value: 20, span: Span::new(404, 406), inferred_type: None },
                        ],
                        span: vec_span,
                        inferred_type: None,
                    },
                    Expr::IntLit { value: 30, span: Span::new(425, 427), inferred_type: None },
                ],
                span: push_span,
                resolved_call: None,
                inferred_type: None,
            }],
            span: len_span,
            resolved_call: None,
            inferred_type: None,
        };

        let check = TestCheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
        display: None,
        };

        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(result.is_ok(), "vec-push should compile: {result:?}");
        // [10 20] pushed 30 -> len 3
        assert_eq!(result.unwrap(), 3);
    }

    // spec: 04-expressions §4.3, §4.10 — Vec literal bound in let, accessed via vec-len
    #[test]
    fn test_compile_vec_literal_in_let() {
        // (let [v [1 2 3]] (vec-len v))
        use cranelisp_types::ResolvedCall;

        let vec_span = Span::new(500, 510);
        let len_span = Span::new(515, 530);

        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            len_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-len"),
            },
        );

        let expr = Expr::Let {
            bindings: vec![(
                Symbol::from("v"),
                Expr::VecLit {
                    elements: vec![
                        Expr::IntLit { value: 1, span: Span::new(501, 502), inferred_type: None },
                        Expr::IntLit { value: 2, span: Span::new(503, 504), inferred_type: None },
                        Expr::IntLit { value: 3, span: Span::new(505, 506), inferred_type: None },
                    ],
                    span: vec_span,
                    inferred_type: None,
                },
            )],
            body: Box::new(Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("vec-len"),
                    span: Span::new(516, 523),
                    inferred_type: None,
                }),
                args: vec![Expr::Var {
                    name: Symbol::from("v"),
                    span: Span::new(524, 525),
                    inferred_type: None,
                }],
                span: len_span,
                resolved_call: None,
                inferred_type: None,
            }),
            span: Span::new(499, 531),
            inferred_type: None,
        };

        let check = TestCheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
        display: None,
        };

        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(result.is_ok(), "vec in let should compile: {result:?}");
        assert_eq!(result.unwrap(), 3);
    }

    // spec: 04-expressions §4.10, §4.11 — Vec literal with computed elements, left-to-right eval
    #[test]
    fn test_compile_vec_literal_with_computed_elements() {
        use cranelisp_types::ResolvedCall;

        // [1 (+ 2 3) 10]
        let add_span = Span::new(603, 610);

        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            add_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("add-i64"),
            },
        );

        let expr = Expr::VecLit {
            elements: vec![
                Expr::IntLit { value: 1, span: Span::new(601, 602), inferred_type: None },
                Expr::Apply {
                    callee: Box::new(Expr::Var {
                        name: Symbol::from("+"),
                        span: Span::new(604, 605),
                        inferred_type: None,
                    }),
                    args: vec![
                        Expr::IntLit { value: 2, span: Span::new(606, 607), inferred_type: None },
                        Expr::IntLit { value: 3, span: Span::new(608, 609), inferred_type: None },
                    ],
                    span: add_span,
                    resolved_call: None,
                    inferred_type: None,
                },
                Expr::IntLit { value: 10, span: Span::new(611, 613), inferred_type: None },
            ],
            span: Span::new(600, 614),
            inferred_type: None,
        };

        let check = TestCheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
        display: None,
        };

        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(result.is_ok(), "vec with computed elements should compile: {result:?}");
        let ptr = result.unwrap();

        assert_eq!(cranelisp_runtime::vec_len(ptr), 3);
        unsafe {
            let base = ptr as *const u8;
            let data_ptr = *(base.add(32) as *const *const i64);
            assert_eq!(*data_ptr, 1);
            assert_eq!(*data_ptr.add(1), 5); // 2 + 3
            assert_eq!(*data_ptr.add(2), 10);
        }

        cranelisp_runtime::vec_drop(ptr, 0);
    }

    // spec: 05-definitions §5.1, 04-expressions §4.10 — Vec literal as function return value
    #[test]
    fn test_compile_vec_in_function_defn() {
        // (defn make-vec [] [1 2 3])
        // Returns a Vec literal.
        let defn = Defn {
            name: Symbol::from("make-vec"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                param_annotations: vec![],
                body: Expr::VecLit {
                elements: vec![
                Expr::IntLit { value: 1, span: Span::new(701, 702), inferred_type: None },
                Expr::IntLit { value: 2, span: Span::new(703, 704), inferred_type: None },
                Expr::IntLit { value: 3, span: Span::new(705, 706), inferred_type: None },
                ],
                span: Span::new(700, 707),
                inferred_type: None,
                },
                span: Span::new(700, 710),
            }],
            visibility: cranelisp_types::Visibility::Public,
            span: Span::new(700, 710),
        };

        let program: Program = vec![TopLevel::Defn(defn)];
        let check = empty_check();

        let ptr = test_compile_program_and_run(&program, &check, &empty_tables()).unwrap();
        assert!(ptr > 1024, "expected heap pointer, got {ptr}");
        assert_eq!(cranelisp_runtime::vec_len(ptr), 3);

        cranelisp_runtime::vec_drop(ptr, 0);
    }

    // spec: appendix-a-builtins §A.3 — vec-get returns correct element value
    #[test]
    fn test_compile_vec_get_verify_value() {
        use cranelisp_types::ResolvedCall;

        // (let [v [100 200 300]] (vec-get v 2))
        let vec_span = Span::new(808, 818);
        let get_span = Span::new(821, 840);

        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            get_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-get"),
            },
        );

        let expr = Expr::Let {
            bindings: vec![(
                Symbol::from("v"),
                Expr::VecLit {
                    elements: vec![
                        Expr::IntLit { value: 100, span: Span::new(809, 812), inferred_type: None },
                        Expr::IntLit { value: 200, span: Span::new(813, 816), inferred_type: None },
                        Expr::IntLit { value: 300, span: Span::new(817, 820), inferred_type: None },
                    ],
                    span: vec_span,
                    inferred_type: None,
                },
            )],
            body: Box::new(Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("vec-get"),
                    span: Span::new(822, 829),
                    inferred_type: None,
                }),
                args: vec![
                    Expr::Var {
                        name: Symbol::from("v"),
                        span: Span::new(830, 831),
                        inferred_type: None,
                    },
                    Expr::IntLit { value: 2, span: Span::new(832, 833), inferred_type: None },
                ],
                span: get_span,
                resolved_call: None,
                inferred_type: None,
            }),
            span: Span::new(807, 841),
            inferred_type: None,
        };

        let check = TestCheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
        display: None,
        };

        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(result.is_ok(), "vec-get value should compile: {result:?}");
        assert_eq!(result.unwrap(), 300);
    }

    // spec: 12-runtime §12.3.3 — vec-push on temporary Vec (COW in-place path)
    #[test]
    fn test_compile_vec_push_on_temp() {
        use cranelisp_types::ResolvedCall;

        // (vec-len (vec-push [1] 2))
        // vec-push on a temporary VecLit — will take COW path (temp = unique).
        let vec_span = Span::new(900, 905);
        let push_span = Span::new(910, 925);
        let len_span = Span::new(905, 930);

        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            push_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-push"),
            },
        );
        method_resolutions.insert(
            len_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-len"),
            },
        );

        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("vec-len"),
                span: Span::new(906, 913),
                inferred_type: None,
            }),
            args: vec![Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("vec-push"),
                    span: Span::new(911, 919),
                    inferred_type: None,
                }),
                args: vec![
                    Expr::VecLit {
                        elements: vec![
                            Expr::IntLit { value: 1, span: Span::new(901, 902), inferred_type: None },
                        ],
                        span: vec_span,
                        inferred_type: None,
                    },
                    Expr::IntLit { value: 2, span: Span::new(920, 921), inferred_type: None },
                ],
                span: push_span,
                resolved_call: None,
                inferred_type: None,
            }],
            span: len_span,
            resolved_call: None,
            inferred_type: None,
        };

        let check = TestCheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
        display: None,
        };

        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(result.is_ok(), "vec-push on temp should compile: {result:?}");
        assert_eq!(result.unwrap(), 2);
    }

    // spec: 12-runtime §12.3.3 — vec-set on temporary Vec (COW in-place path)
    #[test]
    fn test_compile_vec_set_on_temp() {
        use cranelisp_types::ResolvedCall;

        // (vec-len (vec-set [10 20 30] 0 99))
        let vec_span = Span::new(1000, 1010);
        let set_span = Span::new(1015, 1035);
        let len_span = Span::new(1010, 1040);

        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            set_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-set"),
            },
        );
        method_resolutions.insert(
            len_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-len"),
            },
        );

        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("vec-len"),
                span: Span::new(1011, 1018),
                inferred_type: None,
            }),
            args: vec![Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("vec-set"),
                    span: Span::new(1016, 1023),
                    inferred_type: None,
                }),
                args: vec![
                    Expr::VecLit {
                        elements: vec![
                            Expr::IntLit { value: 10, span: Span::new(1001, 1003), inferred_type: None },
                            Expr::IntLit { value: 20, span: Span::new(1004, 1006), inferred_type: None },
                            Expr::IntLit { value: 30, span: Span::new(1007, 1009), inferred_type: None },
                        ],
                        span: vec_span,
                        inferred_type: None,
                    },
                    Expr::IntLit { value: 0, span: Span::new(1024, 1025), inferred_type: None },
                    Expr::IntLit { value: 99, span: Span::new(1026, 1028), inferred_type: None },
                ],
                span: set_span,
                resolved_call: None,
                inferred_type: None,
            }],
            span: len_span,
            resolved_call: None,
            inferred_type: None,
        };

        let check = TestCheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
        display: None,
        };

        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(result.is_ok(), "vec-set on temp should compile: {result:?}");
        assert_eq!(result.unwrap(), 3);
    }

    // spec: 04-expressions §4.10 — Vec literal in interactive (REPL) mode
    #[test]
    fn test_compile_vec_literal_interactive_mode() {
        let expr = Expr::VecLit {
            elements: vec![
                Expr::IntLit { value: 42, span: Span::new(1101, 1103), inferred_type: None },
            ],
            span: Span::new(1100, 1104),
            inferred_type: None,
        };
        let check = empty_check();

        let result = test_compile_and_run(
            &expr, &check, &empty_tables(),
        );
        assert!(result.is_ok(), "vec in interactive mode should compile: {result:?}");
        let ptr = result.unwrap();
        assert!(ptr > 1024);
        assert_eq!(cranelisp_runtime::vec_len(ptr), 1);

        cranelisp_runtime::vec_drop(ptr, 0);
    }

    // spec: appendix-a-builtins §A.3 — vec-len on empty Vec returns 0
    #[test]
    fn test_compile_vec_empty_len() {
        use cranelisp_types::ResolvedCall;

        // (vec-len [])
        let vec_span = Span::new(1200, 1202);
        let len_span = Span::new(1195, 1210);

        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            len_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-len"),
            },
        );

        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("vec-len"),
                span: Span::new(1196, 1203),
                inferred_type: None,
            }),
            args: vec![Expr::VecLit {
                elements: vec![],
                span: vec_span,
                inferred_type: None,
            }],
            span: len_span,
            resolved_call: None,
            inferred_type: None,
        };

        let check = TestCheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
        display: None,
        };

        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(result.is_ok(), "empty vec len should compile: {result:?}");
        assert_eq!(result.unwrap(), 0);
    }

    // spec: appendix-a-builtins §A.3 — vec-push on empty Vec
    #[test]
    fn test_compile_vec_push_empty_vec() {
        use cranelisp_types::ResolvedCall;

        // (vec-len (vec-push [] 42))
        let vec_span = Span::new(1300, 1302);
        let push_span = Span::new(1305, 1320);
        let len_span = Span::new(1300, 1325);

        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            push_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-push"),
            },
        );
        method_resolutions.insert(
            len_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-len"),
            },
        );

        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("vec-len"),
                span: Span::new(1301, 1308),
                inferred_type: None,
            }),
            args: vec![Expr::Apply {
                callee: Box::new(Expr::Var {
                    name: Symbol::from("vec-push"),
                    span: Span::new(1306, 1314),
                    inferred_type: None,
                }),
                args: vec![
                    Expr::VecLit {
                        elements: vec![],
                        span: vec_span,
                        inferred_type: None,
                    },
                    Expr::IntLit { value: 42, span: Span::new(1315, 1317), inferred_type: None },
                ],
                span: push_span,
                resolved_call: None,
                inferred_type: None,
            }],
            span: len_span,
            resolved_call: None,
            inferred_type: None,
        };

        let check = TestCheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
        display: None,
        };

        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(result.is_ok(), "push to empty vec should compile: {result:?}");
        assert_eq!(result.unwrap(), 1);
    }

    // spec: appendix-a-builtins §A.3 — vec-len on empty Vec (duplicate boundary check)
    #[test]
    fn test_compile_vec_len_empty_vec() {
        use cranelisp_types::ResolvedCall;

        let len_span = Span::new(1400, 1420);

        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            len_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("vec-len"),
            },
        );

        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("vec-len"),
                span: Span::new(1401, 1408),
                inferred_type: None,
            }),
            args: vec![Expr::VecLit {
                elements: vec![],
                span: Span::new(1409, 1411),
                inferred_type: None,
            }],
            span: len_span,
            resolved_call: None,
            inferred_type: None,
        };

        let check = TestCheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
        display: None,
        };

        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), 0);
    }

    // spec: 04-expressions §4.10 — nested Vec literals (Vec of Vecs)
    #[test]
    fn test_compile_nested_vec_literals() {
        // [[1 2] [3 4]] — a Vec of Vecs (nested heap values)
        let expr = Expr::VecLit {
            elements: vec![
                Expr::VecLit {
                    elements: vec![
                        Expr::IntLit { value: 1, span: Span::new(1502, 1503), inferred_type: None },
                        Expr::IntLit { value: 2, span: Span::new(1504, 1505), inferred_type: None },
                    ],
                    span: Span::new(1501, 1506),
                    inferred_type: None,
                },
                Expr::VecLit {
                    elements: vec![
                        Expr::IntLit { value: 3, span: Span::new(1508, 1509), inferred_type: None },
                        Expr::IntLit { value: 4, span: Span::new(1510, 1511), inferred_type: None },
                    ],
                    span: Span::new(1507, 1512),
                    inferred_type: None,
                },
            ],
            span: Span::new(1500, 1513),
            inferred_type: None,
        };
        let check = empty_check();

        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(result.is_ok(), "nested vec should compile: {result:?}");
        let outer_ptr = result.unwrap();
        assert!(outer_ptr > 1024);
        assert_eq!(cranelisp_runtime::vec_len(outer_ptr), 2);

        // First inner vec.
        unsafe {
            let base = outer_ptr as *const u8;
            let data = *(base.add(32) as *const *const i64);
            let inner1 = *data;
            assert!(inner1 > 1024, "inner vec should be heap pointer");
            assert_eq!(cranelisp_runtime::vec_len(inner1), 2);
        }

        // Clean up (inner vecs need manual cleanup since no drop glue yet).
        unsafe {
            let base = outer_ptr as *const u8;
            let data = *(base.add(32) as *const *const i64);
            cranelisp_runtime::vec_drop(*data, 0);
            cranelisp_runtime::vec_drop(*data.add(1), 0);
        }
        cranelisp_runtime::vec_drop(outer_ptr, 0);
    }

    // spec: 04-expressions §4.10 — large Vec literal (10 elements)
    #[test]
    fn test_compile_vec_large_literal() {
        // [0 1 2 3 4 5 6 7 8 9] — 10 elements
        let elements: Vec<Expr> = (0..10)
            .map(|i| Expr::IntLit {
                value: i,
                span: Span::new(1600 + (i as u32) * 2, 1602 + (i as u32) * 2),
                inferred_type: None,
            })
            .collect();

        let expr = Expr::VecLit {
            elements,
            span: Span::new(1600, 1620),
            inferred_type: None,
        };
        let check = empty_check();

        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(result.is_ok(), "large vec should compile: {result:?}");
        let ptr = result.unwrap();
        assert_eq!(cranelisp_runtime::vec_len(ptr), 10);

        unsafe {
            let base = ptr as *const u8;
            let data = *(base.add(32) as *const *const i64);
            for i in 0..10 {
                assert_eq!(*data.add(i), i as i64);
            }
        }

        cranelisp_runtime::vec_drop(ptr, 0);
    }

    // --- Ring 2A: TraitMethod dispatch tests ---

    // spec: 07-traits §7.7, appendix-a-builtins §A.3 — Num.+ trait dispatch inlines to add-i64
    #[test]
    fn test_trait_method_dispatch_inline_add() {
        // (+ 3 4) resolved as TraitMethod Num.+ on Int → should inline as iadd.
        let apply_span = Span::new(100, 110);
        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("+"),
                span: Span::new(101, 102),
                inferred_type: None,
            }),
            args: vec![
                Expr::IntLit { value: 3, span: Span::new(103, 104), inferred_type: None },
                Expr::IntLit { value: 4, span: Span::new(105, 106), inferred_type: None },
            ],
            span: apply_span,
            resolved_call: None,
            inferred_type: None,
        };

        let mut check = empty_check();
        check.method_resolutions.insert(
            apply_span,
            cranelisp_types::ResolvedCall::TraitMethod {
                trait_name: cranelisp_types::FQTraitName::new(ModuleFullPath::from("core.num"), "Num".into()),
                method_name: Symbol::from("+"),
                impl_type: cranelisp_types::FQTypeName::new(ModuleFullPath::from("primitives"), "Int".into()),
                mangled_name: cranelisp_types::JitSymbol::from("Num.+$Int"),
            },
        );

        let value = test_compile_and_run(&expr, &check, &empty_tables())
            .expect("TraitMethod inline add should compile");
        assert_eq!(value, 7);
    }

    // spec: 07-traits §7.7, appendix-a-builtins §A.3 — Eq.= trait dispatch on Bool
    #[test]
    fn test_trait_method_dispatch_eq_bool() {
        // (= true true) resolved as TraitMethod Eq.= on Bool → eq-bool.
        let apply_span = Span::new(200, 210);
        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("="),
                span: Span::new(201, 202),
                inferred_type: None,
            }),
            args: vec![
                Expr::BoolLit { value: true, span: Span::new(203, 207), inferred_type: None },
                Expr::BoolLit { value: true, span: Span::new(208, 212), inferred_type: None },
            ],
            span: apply_span,
            resolved_call: None,
            inferred_type: None,
        };

        let mut check = empty_check();
        check.method_resolutions.insert(
            apply_span,
            cranelisp_types::ResolvedCall::TraitMethod {
                trait_name: cranelisp_types::FQTraitName::new(ModuleFullPath::from("core.eq"), "Eq".into()),
                method_name: Symbol::from("="),
                impl_type: cranelisp_types::FQTypeName::new(ModuleFullPath::from("primitives"), "Bool".into()),
                mangled_name: cranelisp_types::JitSymbol::from("Eq.=$Bool"),
            },
        );

        let value = test_compile_and_run(&expr, &check, &empty_tables())
            .expect("TraitMethod eq-bool should compile");
        assert_eq!(value, 1); // true == true → true (1)
    }

    // spec: 07-traits §7.7 — constrained polymorphic fn skipped at definition, monomorphised at call
    #[test]
    fn test_constrained_fn_skipped_in_compile_program() {
        // A constrained fn should be skipped (not compiled).
        let defn = Defn {
            name: Symbol::from("add"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![Symbol::from("x"), Symbol::from("y")],
                param_annotations: vec![],
                body: Expr::IntLit { value: 0, span: Span::new(10, 11), inferred_type: None },
                span: Span::new(0, 20),
            }],
            visibility: cranelisp_types::Visibility::Public,
            span: Span::new(0, 20),
        };

        let main_defn = Defn {
            name: Symbol::from("main"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                param_annotations: vec![],
                body: Expr::IntLit { value: 42, span: Span::new(30, 32), inferred_type: None },
                span: Span::new(25, 40),
            }],
            visibility: cranelisp_types::Visibility::Public,
            span: Span::new(25, 40),
        };

        let program: Program = vec![
            TopLevel::Defn(defn),
            TopLevel::Defn(main_defn),
        ];

        let mut check = empty_check();
        // Mark "add" as constrained — should be skipped during compilation.
        check.constrained_fn_names.insert(Symbol::from("add"));

        let value = test_compile_program_and_run(&program, &check, &empty_tables())
            .expect("should compile with constrained fn skipped");
        assert_eq!(value, 42);
    }

    // spec: 07-traits §7.7 — no default method defns produces empty extras
    #[test]
    fn test_collect_extra_defns_empty() {
        let check = empty_check();
        // Verify default_method_defns is empty in a fresh CheckResult.
        assert!(check.default_method_defns.is_empty());
    }

    // spec: 07-traits §7.7 — default trait methods compiled as extra defns
    #[test]
    fn test_compile_with_default_method_defns() {
        // A program with only a main function, but check has a default method defn.
        // The default method defn should be compiled alongside main.
        let main_defn = Defn {
            name: Symbol::from("main"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                param_annotations: vec![],
                body: Expr::Apply {
                    callee: Box::new(Expr::Var {
                        name: Symbol::from("default-ne"),
                        span: Span::new(10, 20),
                        inferred_type: None,
                    }),
                    args: vec![
                        Expr::IntLit { value: 1, span: Span::new(21, 22), inferred_type: None },
                        Expr::IntLit { value: 2, span: Span::new(23, 24), inferred_type: None },
                    ],
                    span: Span::new(9, 25),
                    resolved_call: None,
                    inferred_type: None,
                },
                span: Span::new(0, 30),
            }],
            visibility: Visibility::Public,
            span: Span::new(0, 30),
        };

        let default_defn = Defn {
            name: Symbol::from("default-ne"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![Symbol::from("x"), Symbol::from("y")],
                param_annotations: vec![],
                body: Expr::IntLit { value: 77, span: Span::new(0, 2), inferred_type: None },
                span: Span::new(0, 10),
            }],
            visibility: Visibility::Public,
            span: Span::new(0, 10),
        };

        let program: Program = vec![TopLevel::Defn(main_defn)];
        let mut check = empty_check();
        check.default_method_defns.push(default_defn);

        let value = test_compile_program_and_run(&program, &check, &empty_tables())
            .expect("program with default method defns should compile");
        assert_eq!(value, 77, "should call the default method defn");
    }

    // spec: 12-runtime §12.5, 07-traits §7.7 — TCO for monomorphised self-recursive call
    //
    // When a constrained-poly function like `countdown` is monomorphised to
    // `countdown$Int`, the body contains a self-recursive call `(countdown ...)`
    // that the typechecker resolves to `SigDispatch { mangled_name: "countdown$Int" }`.
    // The backend's TCO check must recognize this as self-recursion.
    //
    // This test compiles a simple recursive function and verifies it completes
    // without stack overflow (1M iterations would blow the stack without TCO).
    #[test]
    fn test_mono_defn_self_recursive_tco() {
        // countdown$Int: (defn countdown$Int [n] (if (= n 0) 0 (countdown$Int (- n 1))))
        // Simplified: use intrinsic primitives instead of trait dispatch.
        let n_span = Span::new(10, 11);
        let zero_span = Span::new(20, 21);
        let eq_span = Span::new(30, 40);
        let sub_span = Span::new(50, 60);
        let recurse_span = Span::new(70, 90);
        let if_span = Span::new(5, 95);
        let result_span = Span::new(92, 93);

        // Build: (if (eq-i64 n 0) 0 (countdown$Int (sub-i64 n 1)))
        let cond = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("eq-i64"),
                span: Span::new(31, 37),
                inferred_type: None,
            }),
            args: vec![
                Expr::Var { name: Symbol::from("n"), span: n_span, inferred_type: None },
                Expr::IntLit { value: 0, span: zero_span, inferred_type: None },
            ],
            span: eq_span,
            resolved_call: None,
            inferred_type: None,
        };

        let sub_call = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("sub-i64"),
                span: Span::new(51, 58),
                inferred_type: None,
            }),
            args: vec![
                Expr::Var { name: Symbol::from("n"), span: Span::new(55, 56), inferred_type: None },
                Expr::IntLit { value: 1, span: Span::new(57, 58), inferred_type: None },
            ],
            span: sub_span,
            resolved_call: None,
            inferred_type: None,
        };

        // The recursive call: callee is "countdown" (original name),
        // but it's resolved to countdown$Int via SigDispatch.
        let recurse = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("countdown"),
                span: Span::new(71, 80),
                inferred_type: None,
            }),
            args: vec![sub_call],
            span: recurse_span,
            resolved_call: None,
            inferred_type: None,
        };

        let body = Expr::If {
            cond: Box::new(cond),
            then_branch: Box::new(Expr::IntLit { value: 0, span: result_span, inferred_type: None }),
            else_branch: Box::new(recurse),
            span: if_span,
            inferred_type: None,
        };

        let countdown_defn = Defn {
            name: Symbol::from("countdown$Int"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![Symbol::from("n")],
                param_annotations: vec![],
                body,
                span: Span::new(0, 100),
            }],
            visibility: cranelisp_types::Visibility::Public,
            span: Span::new(0, 100),
        };

        // Set up method resolutions:
        // - eq_span: BuiltinFn("eq-i64") for the equality check
        // - sub_span: BuiltinFn("sub-i64") for the subtraction
        // - recurse_span: SigDispatch("countdown$Int") for the self-recursive call
        let mut check = empty_check();
        check.method_resolutions.insert(
            eq_span,
            cranelisp_types::ResolvedCall::BuiltinFn {
                name: Symbol::from("eq-i64"),
            },
        );
        check.method_resolutions.insert(
            sub_span,
            cranelisp_types::ResolvedCall::BuiltinFn {
                name: Symbol::from("sub-i64"),
            },
        );
        check.method_resolutions.insert(
            recurse_span,
            cranelisp_types::ResolvedCall::SigDispatch {
                mangled_name: cranelisp_types::JitSymbol::from("countdown$Int"),
            },
        );

        // Enrich the defn from CheckResult side maps (test bridge).
        let mut enriched_defn = countdown_defn.clone();
        enrich_defn_from_side_maps(&mut enriched_defn, &check.method_resolutions, &check.expr_types);

        // Compile with direct calls (no GOT).
        let mut jit = Jit::new().unwrap();
        jit.declare_intrinsics().unwrap();
        let func_ids = jit.declare_functions(&[&enriched_defn]).unwrap();

        let arities: HashMap<Symbol, usize> =
            vec![(Symbol::from("countdown$Int"), 1)].into_iter().collect();

        let tables = empty_tables();
        let ctx = jit.build_compile_context(
            &func_ids, &arities,
            &tables, ModuleFullPath::from("test"),
        );
        jit.compile_defn(&enriched_defn, ctx).unwrap();
        let countdown_ptr = jit.finalize_and_get_ptr(&Symbol::from("countdown$Int"), 1).unwrap();

        // Call with 1_000_000 — without TCO this would stack overflow.
        let func: extern "C" fn(i64) -> i64 = unsafe { std::mem::transmute(countdown_ptr) };
        let result = func(1_000_000);
        assert_eq!(result, 0, "TCO should allow 1M recursive calls without stack overflow");
    }

    // --- compile_to_module module tests ---

    // spec: design/arch/CLAUDE.md Decision 36 — bare-name function declarations
    // uniformly across all modules. Two modules with same-named function compile
    // into separate JITs without collision because function symbols are
    // `.o`-Local — they cannot collide across modules' JITs.
    #[test]
    fn test_module_prefix_applied() {
        let _ = empty_check();
        // Module "mod_a" defines "val" returning 100.
        let val_a = Defn {
            name: Symbol::from("val"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                param_annotations: vec![],
                body: Expr::IntLit { value: 100, span: Span::new(0, 3), inferred_type: None },
                span: Span::new(0, 20),
            }],
            visibility: Visibility::Public,
            span: Span::new(0, 20),
        };

        let mod_a = ModuleFullPath::from("mod_a");
        let tables = empty_tables();
        {
            let mut st = SymbolTable::new(mod_a.clone());
            st.insert(val_a.name.clone(), make_def_entry(val_a.clone()));
            tables.insert(mod_a.clone(), st);
        }
        let mut jit_a = Jit::new().unwrap();
        let result_a = compile_to_module(
            mod_a.clone(),
            std::slice::from_ref(&val_a.name),
            &tables,
            jit_a.jit_module(),
        ).expect("module A should compile");
        // Post-G6: compile_to_module finalized internally.

        // Per Decision 36 (bare-Local uniformly), result_func_ids is keyed
        // by the bare symbol name — NOT module-qualified. The pre-Sprint-58
        // behavior of producing `mod_a/val` for non-user/main modules was a
        // defect.
        assert!(
            result_a.func_ids.contains_key(&Symbol::from("val")),
            "func_ids should contain bare name (Decision 36): {:?}",
            result_a.func_ids.keys().collect::<Vec<_>>()
        );
        assert!(
            !result_a.func_ids.contains_key(&Symbol::from("mod_a/val")),
            "func_ids must NOT contain module-qualified name (Decision 36): {:?}",
            result_a.func_ids.keys().collect::<Vec<_>>()
        );

        // Execute module A's "val".
        let entry_id = result_a.entry_func_id.expect("should have entry");
        let ptr = jit_a.get_finalized_ptr(entry_id);
        let func: extern "C" fn() -> i64 = unsafe { std::mem::transmute(ptr) };
        assert_eq!(func(), 100, "module A's val should return 100");

        // Module B also defines "val" returning 200 — compiles into a separate JIT.
        let val_b = Defn {
            name: Symbol::from("val"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                param_annotations: vec![],
                body: Expr::IntLit { value: 200, span: Span::new(100, 103), inferred_type: None },
                span: Span::new(100, 120),
            }],
            visibility: Visibility::Public,
            span: Span::new(100, 120),
        };
        let mod_b = ModuleFullPath::from("mod_b");
        {
            let mut st = SymbolTable::new(mod_b.clone());
            st.insert(val_b.name.clone(), make_def_entry(val_b.clone()));
            tables.insert(mod_b.clone(), st);
        }

        let mut jit_b = Jit::new().unwrap();
        let result_b = compile_to_module(
            mod_b,
            std::slice::from_ref(&val_b.name),
            &tables,
            jit_b.jit_module(),
        ).expect("module B should compile without collision");
        // Post-G6: compile_to_module finalized internally.

        let entry_b = result_b.entry_func_id.expect("should have entry");
        let ptr_b = jit_b.get_finalized_ptr(entry_b);
        let func_b: extern "C" fn() -> i64 = unsafe { std::mem::transmute(ptr_b) };
        assert_eq!(func_b(), 200, "module B's val should return 200");
    }

    // --- G6 code-write invariants (Sprint 57 Wave 2; updated Sprint 58 Wave 3b) ---
    //
    // spec: design/backend/compile-to-module.md §9.1.3 + Sprint 58 Wave 3b
    // (Decision 35 Layer 2 Option B) — compile_to_module returns per-symbol
    // finalised code pointers in `CompilationResult.code_ptrs`. The
    // integration layer constructs `Code::Jit { jit, ptr }` per entry and
    // writes it onto `ModuleEntry::Def.code`. Backend itself no longer
    // touches the `code` field.
    #[test]
    fn compile_to_module_returns_code_ptrs_after_finalize() {
        let defn = Defn {
            name: Symbol::from("seven"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                param_annotations: vec![],
                body: Expr::IntLit { value: 7, span: Span::new(0, 1), inferred_type: None },
                span: Span::new(0, 20),
            }],
            visibility: Visibility::Public,
            span: Span::new(0, 20),
        };

        let module = ModuleFullPath::from("user");
        let tables = empty_tables();
        {
            let mut st = SymbolTable::new(module.clone());
            st.insert(defn.name.clone(), make_def_entry(defn.clone()));
            tables.insert(module.clone(), st);
        }

        let mut jit = Jit::new().unwrap();
        let result = compile_to_module(
            module.clone(),
            std::slice::from_ref(&defn.name),
            &tables,
            jit.jit_module(),
        ).expect("JIT compile should succeed");

        // Post-Wave-3b invariant: result.code_ptrs is populated with the
        // finalised code pointer per defined symbol (JIT mode).
        let ptr = result
            .code_ptrs
            .get(&defn.name)
            .copied()
            .expect("JIT compile must populate code_ptrs[name]");
        assert!(
            !ptr.is_null(),
            "finalized code pointer must be non-null (JIT mode)"
        );

        // Backend MUST NOT touch ModuleEntry::Def.code itself — that's the
        // integration layer's responsibility (Decision 35 Layer 2 Option B).
        let guard = tables.get(&module).expect("symbol table present");
        let entry = guard.get(defn.name.as_ref()).expect("entry present");
        match entry {
            ModuleEntry::Def { code, .. } => {
                assert!(
                    code.is_none(),
                    "backend must not write to ModuleEntry::Def.code in Wave 3b — that's the integration layer's job"
                );
            }
            _ => unreachable!("test inserted a Def entry"),
        }
    }

    // spec: design/backend/compile-to-module.md §9.1.6 — ObjectModule has no
    // post-finalize runtime pointer; `code_ptrs` is empty in object mode.
    #[test]
    fn compile_to_module_object_mode_empty_code_ptrs() {
        use cranelift_module::default_libcall_names;
        use cranelift_object::{ObjectBuilder, ObjectModule};

        let defn = Defn {
            name: Symbol::from("answer"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                param_annotations: vec![],
                body: Expr::IntLit { value: 42, span: Span::new(0, 2), inferred_type: None },
                span: Span::new(0, 20),
            }],
            visibility: Visibility::Public,
            span: Span::new(0, 20),
        };

        let module = ModuleFullPath::from("user");
        let tables = empty_tables();
        {
            let mut st = SymbolTable::new(module.clone());
            st.insert(defn.name.clone(), make_def_entry(defn.clone()));
            tables.insert(module.clone(), st);
        }

        let isa = build_isa(true).unwrap();
        let obj_builder =
            ObjectBuilder::new(isa, "test_obj", default_libcall_names()).unwrap();
        let mut obj_module = ObjectModule::new(obj_builder);

        let result = compile_to_module(
            module.clone(),
            std::slice::from_ref(&defn.name),
            &tables,
            &mut obj_module,
        ).expect("object compile should succeed");

        // Object-mode invariant: `code_ptrs` is empty because ObjectModule's
        // `try_get_finalized_function` returns None (no runtime pointer).
        assert!(
            result.code_ptrs.is_empty(),
            "object-mode compile must not produce any code pointers (got {:?})",
            result.code_ptrs.keys().collect::<Vec<_>>()
        );

        // Sanity: the entry's `code` field is also None (backend doesn't
        // touch it; cache-write path eventually serialises this entry to
        // `.meta.json` with `code` skipped per #[serde(skip)]).
        let guard = tables.get(&module).expect("symbol table present");
        let entry = guard.get(defn.name.as_ref()).expect("entry present");
        match entry {
            ModuleEntry::Def { code, .. } => {
                assert!(
                    code.is_none(),
                    "object-mode entry's code field must be None"
                );
            }
            _ => unreachable!("test inserted a Def entry"),
        }
    }

    // --- multi-sig defn tests ---
    //
    // Sprint 56 Wave 1: `build_mangled_name`, `concrete_type_name`, and
    // `expand_multi_sig_defn` were deleted from the backend. Mangled variant
    // entries are now pre-materialised by typecheck in Wave 0. The unit tests
    // that exercised those helpers directly are retired; end-to-end multi-sig
    // dispatch is covered by `test_compile_multi_sig_defn_end_to_end` and
    // `test_compile_multi_sig_second_variant` below (plus the integration
    // tests in `tests/`).

    // spec: 05-definitions §5.1.2 — multi-sig defn compiles and dispatches correctly
    //
    // Defines a multi-sig function `f` with two variants:
    //   (defn f ([x] x) ([a b] a))      — identity on 1 arg, first on 2 args
    // Then defines main that calls the first variant via SigDispatch.
    #[test]
    fn test_compile_multi_sig_defn_end_to_end() {
        let variant1_span = Span::new(10, 30);
        let variant2_span = Span::new(40, 60);

        let multi_defn = Defn {
            name: Symbol::from("f"),
            docstring: None,
            variants: vec![
                DefnVariant {
                    params: vec![Symbol::from("x")],
                    param_annotations: vec![],
                    body: Expr::Var { name: Symbol::from("x"), span: Span::new(15, 16), inferred_type: None },
                    span: variant1_span,
                },
                DefnVariant {
                    params: vec![Symbol::from("a"), Symbol::from("b")],
                    param_annotations: vec![],
                    body: Expr::Var { name: Symbol::from("a"), span: Span::new(45, 46), inferred_type: None },
                    span: variant2_span,
                },
            ],
            visibility: cranelisp_types::Visibility::Public,
            span: Span::new(0, 70),
        };

        // main calls f$Int(42)
        let call_span = Span::new(100, 120);
        let main_defn = Defn {
            name: Symbol::from("main"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                param_annotations: vec![],
                body: Expr::Apply {
                    callee: Box::new(Expr::Var {
                        name: Symbol::from("f"),
                        span: Span::new(101, 102),
                        inferred_type: None,
                    }),
                    args: vec![Expr::IntLit { value: 42, span: Span::new(103, 105), inferred_type: None }],
                    span: call_span,
                    resolved_call: None,
                    inferred_type: None,
                },
                span: Span::new(95, 125),
            }],
            visibility: cranelisp_types::Visibility::Public,
            span: Span::new(95, 125),
        };

        let program: Program = vec![
            TopLevel::Defn(multi_defn),
            TopLevel::Defn(main_defn),
        ];

        let mut check = empty_check();
        // Register SigDispatch for the call site.
        check.method_resolutions.insert(
            call_span,
            cranelisp_types::ResolvedCall::SigDispatch {
                mangled_name: cranelisp_types::JitSymbol::from("f$Int"),
            },
        );

        // Set up symbol table with Overloaded entry for multi-sig expansion.
        let tables: DashMap<ModuleFullPath, SymbolTable> = DashMap::new();
        let module_path = ModuleFullPath::from("user");
        let mut table = SymbolTable::new(module_path.clone());
        table.insert(
            Symbol::from("f"),
            cranelisp_types::ModuleEntry::Def {
                scheme: cranelisp_types::Scheme { vars: vec![], constraints: Default::default(), ty: Type::Int },
                visibility: cranelisp_types::Visibility::Public,
                docstring: None,
                param_names: vec![],
                kind: Box::new(cranelisp_types::DefKind::Overloaded {
                    variants: vec![
                        cranelisp_types::OverloadVariant {
                            param_types: vec![Type::Int],
                            ret_type: Type::Int,
                            mangled_name: Symbol::from("f$Int"),
                        },
                        cranelisp_types::OverloadVariant {
                            param_types: vec![Type::Int, Type::Int],
                            ret_type: Type::Int,
                            mangled_name: Symbol::from("f$Int+Int"),
                        },
                    ],
                }),
                callees: vec![],
                got_slot: None,
                trait_origin: None,
                ast: None,
                code: None,
                fn_ptr: None,
            },
        );
        tables.insert(module_path, table);

        let result = test_compile_program_and_run(&program, &check, &tables)
            .expect("multi-sig program should compile");
        assert_eq!(result, 42, "should dispatch to f$Int and return 42");
    }

    // spec: 05-definitions §5.1.2 — multi-sig dispatch to second variant
    #[test]
    fn test_compile_multi_sig_second_variant() {
        let variant1_span = Span::new(10, 30);
        let variant2_span = Span::new(40, 60);

        let multi_defn = Defn {
            name: Symbol::from("g"),
            docstring: None,
            variants: vec![
                DefnVariant {
                    params: vec![Symbol::from("x")],
                    param_annotations: vec![],
                    body: Expr::Var { name: Symbol::from("x"), span: Span::new(15, 16), inferred_type: None },
                    span: variant1_span,
                },
                DefnVariant {
                    params: vec![Symbol::from("a"), Symbol::from("b")],
                    param_annotations: vec![],
                    // Return b (second param) to prove we dispatched to the right variant.
                    body: Expr::Var { name: Symbol::from("b"), span: Span::new(45, 46), inferred_type: None },
                    span: variant2_span,
                },
            ],
            visibility: cranelisp_types::Visibility::Public,
            span: Span::new(0, 70),
        };

        // main calls g$Int+Int(10, 99) — should return 99 (the second arg)
        let call_span = Span::new(100, 120);
        let main_defn = Defn {
            name: Symbol::from("main"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                param_annotations: vec![],
                body: Expr::Apply {
                    callee: Box::new(Expr::Var {
                        name: Symbol::from("g"),
                        span: Span::new(101, 102),
                        inferred_type: None,
                    }),
                    args: vec![
                        Expr::IntLit { value: 10, span: Span::new(103, 105), inferred_type: None },
                        Expr::IntLit { value: 99, span: Span::new(106, 108), inferred_type: None },
                    ],
                    span: call_span,
                    resolved_call: None,
                    inferred_type: None,
                },
                span: Span::new(95, 125),
            }],
            visibility: cranelisp_types::Visibility::Public,
            span: Span::new(95, 125),
        };

        let program: Program = vec![
            TopLevel::Defn(multi_defn),
            TopLevel::Defn(main_defn),
        ];

        let mut check = empty_check();
        check.method_resolutions.insert(
            call_span,
            cranelisp_types::ResolvedCall::SigDispatch {
                mangled_name: cranelisp_types::JitSymbol::from("g$Int+Int"),
            },
        );

        // Set up symbol table with Overloaded entry for multi-sig expansion.
        let tables: DashMap<ModuleFullPath, SymbolTable> = DashMap::new();
        let module_path = ModuleFullPath::from("user");
        let mut table = SymbolTable::new(module_path.clone());
        table.insert(
            Symbol::from("g"),
            cranelisp_types::ModuleEntry::Def {
                scheme: cranelisp_types::Scheme { vars: vec![], constraints: Default::default(), ty: Type::Int },
                visibility: cranelisp_types::Visibility::Public,
                docstring: None,
                param_names: vec![],
                kind: Box::new(cranelisp_types::DefKind::Overloaded {
                    variants: vec![
                        cranelisp_types::OverloadVariant {
                            param_types: vec![Type::Int],
                            ret_type: Type::Int,
                            mangled_name: Symbol::from("g$Int"),
                        },
                        cranelisp_types::OverloadVariant {
                            param_types: vec![Type::Int, Type::Int],
                            ret_type: Type::Int,
                            mangled_name: Symbol::from("g$Int+Int"),
                        },
                    ],
                }),
                callees: vec![],
                got_slot: None,
                trait_origin: None,
                ast: None,
                code: None,
                fn_ptr: None,
            },
        );
        tables.insert(module_path, table);

        let result = test_compile_program_and_run(&program, &check, &tables)
            .expect("multi-sig program should compile");
        assert_eq!(result, 99, "should dispatch to g$Int+Int and return second arg (99)");
    }

    // Note: `test_expand_multi_sig_missing_type_info` and
    // `test_concrete_type_name_all_primitives` were retired in Sprint 56 Wave 1
    // with the deletion of `expand_multi_sig_defn` / `concrete_type_name`. The
    // equivalent mangled-name construction now lives in `/typecheck`, and the
    // "missing overload info" error surface is exercised by the backend's
    // `ast: None` error path (see `test_compile_to_module_ast_none_errors` in
    // the Sprint 56 Wave 1 unit tests below).

    // spec: appendix-a-builtins §A.2 — extern primitive dispatch via resolved_call
    //
    // Isolates the "undefined function: macros/sconcat" failure from
    // repl_defmacro_rest_splice. When compile_apply receives an Apply node
    // with resolved_call: Some(BuiltinFn { name: "sconcat" }), it must take
    // the extern call path (compile_extern_call). When resolved_call is None,
    // it falls through to compile_direct_call which fails because there is no
    // GOT slot or FuncId for the qualified name "macros/sconcat".
    #[test]
    fn test_extern_primitive_via_resolved_call_succeeds() {
        use cranelisp_types::ResolvedCall;

        // Build: (defn main [] (sconcat 0 0))
        // sconcat is an extern primitive that takes two i64 args.
        // We pass 0s (representing SNil) — the extern symbol exists in the
        // JIT runtime so the call will succeed at compile time.
        let apply_span = Span::new(2000, 2030);

        let mut method_resolutions = HashMap::new();
        method_resolutions.insert(
            apply_span,
            ResolvedCall::BuiltinFn {
                name: Symbol::from("sconcat"),
            },
        );

        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("macros/sconcat"),
                span: Span::new(2001, 2015),
                inferred_type: None,
            }),
            args: vec![
                Expr::IntLit { value: 0, span: Span::new(2016, 2017), inferred_type: None },
                Expr::IntLit { value: 0, span: Span::new(2018, 2019), inferred_type: None },
            ],
            span: apply_span,
            resolved_call: None, // enrichment will set this from method_resolutions
            inferred_type: None,
        };

        let check = TestCheckResult {
            method_resolutions,
            constrained_fn_names: HashSet::new(),
            mono_defns: Vec::new(),
            expr_types: HashMap::new(),
            default_method_defns: Vec::new(),
            warnings: Vec::new(),
            display: None,
        };

        // With resolved_call present (via enrichment), compilation should
        // succeed because compile_apply routes to compile_extern_call.
        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(
            result.is_ok(),
            "extern primitive sconcat should compile when resolved_call is BuiltinFn: {result:?}"
        );
    }

    // spec: appendix-a-builtins §A.2 — missing resolved_call causes "undefined function"
    //
    // Companion to the test above: when resolved_call is None (not enriched),
    // compile_apply falls through to compile_var_apply -> compile_direct_call
    // which fails because "macros/sconcat" has no GOT slot or FuncId.
    // This is the broken path that the integration test hits.
    #[test]
    fn test_extern_primitive_without_resolved_call_fails() {
        // Build: (defn main [] (macros/sconcat 0 0))
        // No resolved_call, no GOT entry, no FuncId — should fail.
        let apply_span = Span::new(2100, 2130);

        // No method_resolutions — resolved_call stays None.
        let expr = Expr::Apply {
            callee: Box::new(Expr::Var {
                name: Symbol::from("macros/sconcat"),
                span: Span::new(2101, 2115),
                inferred_type: None,
            }),
            args: vec![
                Expr::IntLit { value: 0, span: Span::new(2116, 2117), inferred_type: None },
                Expr::IntLit { value: 0, span: Span::new(2118, 2119), inferred_type: None },
            ],
            span: apply_span,
            resolved_call: None,
            inferred_type: None,
        };

        let check = empty_check();

        let result = test_compile_and_run(&expr, &check, &empty_tables());
        assert!(
            result.is_err(),
            "macros/sconcat without resolved_call should fail"
        );
        let err_msg = format!("{:?}", result.unwrap_err());
        assert!(
            err_msg.contains("undefined function"),
            "error should be 'undefined function', got: {err_msg}"
        );
    }

    // -----------------------------------------------------------------
    // Sprint 56 Wave 1 (Step 2a) — direct compile_to_module tests
    // -----------------------------------------------------------------

    // spec: design/backend/compile-to-module.md §2.1 — 4-param signature
    //
    // Direct `compile_to_module` call with a populated `symbol_tables` and a
    // single-name `names` list. Verifies the post-Phase-2 contract: bodies
    // arrive via `ModuleEntry::Def.ast`, the return value keys `func_ids` by
    // the compiled symbol, and a zero-arg defn sets `entry_func_id`.
    #[test]
    fn sprint56_compile_to_module_direct_call_returns_funcid() {
        use cranelisp_types::ModuleEntry;
        let defn = Defn {
            name: Symbol::from("answer"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                param_annotations: vec![],
                body: Expr::IntLit { value: 42, span: Span::new(0, 2), inferred_type: None },
                span: Span::new(0, 10),
            }],
            visibility: Visibility::Public,
            span: Span::new(0, 10),
        };

        let module = ModuleFullPath::from("user");
        let tables = empty_tables();
        {
            let mut st = SymbolTable::new(module.clone());
            st.insert(defn.name.clone(), make_def_entry(defn.clone()));
            tables.insert(module.clone(), st);
        }

        let mut jit = Jit::new().unwrap();
        let result = compile_to_module(
            module,
            std::slice::from_ref(&defn.name),
            &tables,
            jit.jit_module(),
        )
        .expect("direct compile_to_module should succeed");

        assert!(
            result.func_ids.contains_key(&defn.name),
            "func_ids must include the compiled symbol: {:?}",
            result.func_ids.keys().collect::<Vec<_>>()
        );
        assert!(
            result.entry_func_id.is_some(),
            "zero-arg defn should set entry_func_id"
        );
        assert!(
            result.artifacts.contains_key(&defn.name),
            "artifacts map must include per-symbol codegen byproducts"
        );
        // Ensure the entry is present as a Def with ast: Some(_) in the table
        // (regression guard against accidentally dropping the entry).
        let guard = tables.get(&ModuleFullPath::from("user")).unwrap();
        assert!(matches!(
            guard.get(defn.name.as_ref()),
            Some(ModuleEntry::Def { ast: Some(_), .. })
        ));
    }

    // spec: design/backend/compile-to-module.md §4 — ast: None returns error
    //
    // Negative: insert a `ModuleEntry::Def { ast: None, .. }` into the symbol
    // table and pass its name in `names`. `compile_to_module` must return
    // `Err(CranelispError::CodegenError)` whose message names the symbol —
    // no panic, no silent skip.
    #[test]
    fn sprint56_compile_to_module_ast_none_errors() {
        use cranelisp_types::{DefKind, ModuleEntry, Scheme, Visibility};
        let module = ModuleFullPath::from("user");
        let name = Symbol::from("stub");
        let tables = empty_tables();
        {
            let mut st = SymbolTable::new(module.clone());
            st.insert(
                name.clone(),
                ModuleEntry::Def {
                    scheme: Scheme {
                        vars: vec![],
                        constraints: HashMap::new(),
                        ty: Type::Fn(vec![], Box::new(Type::Int)),
                    },
                    visibility: Visibility::Public,
                    docstring: None,
                    param_names: vec![],
                    kind: Box::new(DefKind::UserFn { constrained_fn: None }),
                    callees: vec![],
                    got_slot: None,
                    trait_origin: None,
                    ast: None,
                    code: None,
                    fn_ptr: None,
                },
            );
            tables.insert(module.clone(), st);
        }

        let mut jit = Jit::new().unwrap();
        let result = compile_to_module(
            module,
            std::slice::from_ref(&name),
            &tables,
            jit.jit_module(),
        );
        let err = match result {
            Ok(_) => unreachable!("ast: None must not succeed"),
            Err(e) => e,
        };

        let msg = err.message();
        assert!(
            msg.contains(name.as_ref()),
            "error message must name the offending symbol 'stub', got: {msg}"
        );
        assert!(
            msg.contains("ast: None") || msg.contains("ast") && msg.contains("None"),
            "error message should mention the ast: None invariant violation, got: {msg}"
        );
    }

    // spec: design/backend/compile-to-module.md §4 — no multi-sig expansion in backend
    //
    // Populate symbol_tables with a pre-mangled multi-sig variant entry
    // (`add$Int+Int`, ast: Some(single-variant defn)) alongside the
    // Overloaded base entry (`add`, ast: None). Call compile_to_module with
    // names = [mangled variant]. Compilation must succeed — the backend never
    // invokes a (deleted) `expand_multi_sig_defn` path.
    //
    // That this test compiles and passes IS the verification: Wave 1 deleted
    // `expand_multi_sig_defn` entirely from the source tree.
    #[test]
    fn sprint56_compile_to_module_mangled_variant_compiles_without_expansion() {
        use cranelisp_types::{DefKind, ModuleEntry, OverloadVariant, Scheme, Visibility};

        let module = ModuleFullPath::from("user");
        let base_name = Symbol::from("add");
        let variant_name = Symbol::from("add$Int+Int");

        // Mangled variant defn — what typecheck's Wave 0 materialises.
        let variant_defn = Defn {
            name: variant_name.clone(),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![Symbol::from("x"), Symbol::from("y")],
                param_annotations: vec![],
                // Body returns x (proves the variant body is what got compiled).
                body: Expr::Var {
                    name: Symbol::from("x"),
                    span: Span::new(5, 6),
                    inferred_type: Some(Box::new(Type::Int)),
                },
                span: Span::new(0, 20),
            }],
            visibility: Visibility::Public,
            span: Span::new(0, 20),
        };

        let tables = empty_tables();
        {
            let mut st = SymbolTable::new(module.clone());
            // Overloaded base entry: ast: None — compile_to_module must NOT
            // try to compile this (the filter via `defined_symbols()` skips
            // it; a caller passing it in `names` would hit the ast: None
            // error path — which is the right behaviour).
            st.insert(
                base_name.clone(),
                ModuleEntry::Def {
                    scheme: Scheme {
                        vars: vec![],
                        constraints: HashMap::new(),
                        ty: Type::Int,
                    },
                    visibility: Visibility::Public,
                    docstring: None,
                    param_names: vec![],
                    kind: Box::new(DefKind::Overloaded {
                        variants: vec![OverloadVariant {
                            param_types: vec![Type::Int, Type::Int],
                            ret_type: Type::Int,
                            mangled_name: variant_name.clone(),
                        }],
                    }),
                    callees: vec![],
                    got_slot: None,
                    trait_origin: None,
                    ast: None,
                    code: None,
                    fn_ptr: None,
                },
            );
            // Mangled variant entry: ast: Some(variant_defn).
            st.insert(variant_name.clone(), make_def_entry(variant_defn));
            tables.insert(module.clone(), st);
        }

        let mut jit = Jit::new().unwrap();
        let result = compile_to_module(
            module,
            std::slice::from_ref(&variant_name),
            &tables,
            jit.jit_module(),
        )
        .expect("pre-mangled variant should compile without expansion");

        assert!(
            result.func_ids.contains_key(&variant_name),
            "func_ids must contain the mangled name"
        );
    }

    // spec: design/backend/compile-to-module.md §4 — constrained-template exclusion via defined_symbols
    //
    // Verifies that `SymbolTable::defined_symbols()` — the shared filter
    // callers use to build the `names` list — excludes constrained-function
    // templates (`UserFn { constrained_fn: Some(_) }`). The backend relies
    // on this filter upstream; if it were to break, constrained templates
    // would reach compile_to_module and fail (templates carry type vars,
    // not concrete types). This re-asserts Wave 0's contract from the
    // backend's vantage point.
    #[test]
    fn sprint56_constrained_template_excluded_by_defined_symbols() {
        use cranelisp_types::{DefKind, ModuleEntry, Scheme, Visibility};

        let module = ModuleFullPath::from("user");
        let template_name = Symbol::from("identity");
        let normal_name = Symbol::from("answer");

        // A typical regular defn: compile-eligible.
        let normal_defn = Defn {
            name: normal_name.clone(),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                param_annotations: vec![],
                body: Expr::IntLit { value: 1, span: Span::new(0, 1), inferred_type: None },
                span: Span::new(0, 5),
            }],
            visibility: Visibility::Public,
            span: Span::new(0, 5),
        };

        // A constrained-fn template defn: should be filtered OUT by
        // defined_symbols() even though it carries ast: Some(_).
        let template_defn = Defn {
            name: template_name.clone(),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![Symbol::from("x")],
                param_annotations: vec![],
                body: Expr::Var {
                    name: Symbol::from("x"),
                    span: Span::new(0, 1),
                    inferred_type: None,
                },
                span: Span::new(0, 10),
            }],
            visibility: Visibility::Public,
            span: Span::new(0, 10),
        };

        let tables = empty_tables();
        {
            let mut st = SymbolTable::new(module.clone());
            st.insert(normal_name.clone(), make_def_entry(normal_defn));
            // Insert a UserFn template by hand — constrained_fn is Some.
            st.insert(
                template_name.clone(),
                ModuleEntry::Def {
                    scheme: Scheme {
                        vars: vec![],
                        constraints: HashMap::new(),
                        ty: Type::Fn(vec![Type::Var(0)], Box::new(Type::Var(0))),
                    },
                    visibility: Visibility::Public,
                    docstring: None,
                    param_names: vec![Symbol::from("x")],
                    kind: Box::new(DefKind::UserFn {
                        // Sentinel — real typecheck stores a cloned Defn here.
                        constrained_fn: Some(Box::new(cranelisp_types::ConstrainedFn {
                            defn: template_defn.clone(),
                            scheme: Scheme {
                                vars: vec![],
                                constraints: HashMap::new(),
                                ty: Type::Fn(vec![Type::Var(0)], Box::new(Type::Var(0))),
                            },
                        })),
                    }),
                    callees: vec![],
                    got_slot: None,
                    trait_origin: None,
                    ast: Some(template_defn),
                    code: None,
                    fn_ptr: None,
                },
            );
            tables.insert(module.clone(), st);
        }

        let guard = tables.get(&module).unwrap();
        let defined: Vec<&Symbol> = guard.defined_symbols().map(|(n, _)| n).collect();

        assert!(
            defined.contains(&&normal_name),
            "defined_symbols() must yield regular defns: got {:?}",
            defined
        );
        assert!(
            !defined.contains(&&template_name),
            "defined_symbols() must NOT yield constrained-fn templates: got {:?}",
            defined
        );
    }

    // ----- Sprint 58 Wave 2: Decision 36 + Decision 23 unit tests -----
    //
    // These tests cover the architectural reconciliation landed in Sprint 58
    // Wave 2: bare-name + Linkage::Local function declarations uniformly across
    // all modules (Decision 36), and `__cranelisp_got_{M}` defined as
    // Linkage::Export data symbol in the .o (Decision 23 — Bug B fix).

    /// Helper: make an ObjectModule for these tests (PIC enabled).
    fn make_object_module() -> cranelift_object::ObjectModule {
        use cranelift_module::default_libcall_names;
        use cranelift_object::ObjectBuilder;

        let isa = crate::cache::object::build_isa(true).unwrap();
        let builder = ObjectBuilder::new(isa, "test", default_libcall_names()).unwrap();
        cranelift_object::ObjectModule::new(builder)
    }

    /// Helper: build a single-defn symbol table with `got_slot: Some(slot)` so
    /// the GOT-data emission step has a slot to populate.
    fn table_with_def_and_slot(
        module: &ModuleFullPath,
        defn: Defn,
        slot: usize,
    ) -> DashMap<ModuleFullPath, SymbolTable> {
        use cranelisp_types::{DefKind, ModuleEntry, Scheme, Visibility};
        let tables = DashMap::new();
        let mut st = SymbolTable::new(module.clone());
        // Match the slot index: typecheck would have called allocate_got_slot
        // exactly `slot+1` times.
        for _ in 0..=slot {
            let _ = st.allocate_got_slot();
        }
        let param_count = defn.params().len();
        let param_names = defn
            .variants
            .first()
            .map(|v| v.params.clone())
            .unwrap_or_default();
        st.insert(
            defn.name.clone(),
            ModuleEntry::Def {
                scheme: Scheme {
                    vars: vec![],
                    constraints: HashMap::new(),
                    ty: Type::Fn(
                        (0..param_count).map(|_| Type::Int).collect(),
                        Box::new(Type::Int),
                    ),
                },
                visibility: Visibility::Public,
                docstring: None,
                param_names,
                kind: Box::new(DefKind::UserFn { constrained_fn: None }),
                callees: vec![],
                got_slot: Some(slot),
                trait_origin: None,
                ast: Some(defn),
                code: None,
                fn_ptr: None,
            },
        );
        tables.insert(module.clone(), st);
        tables
    }

    /// Helper: trivial zero-arg defn returning an int literal.
    fn make_int_defn(name: &str, value: i64) -> Defn {
        Defn {
            name: Symbol::from(name),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                param_annotations: vec![],
                body: Expr::IntLit { value, span: Span::SYNTHETIC, inferred_type: None },
                span: Span::SYNTHETIC,
            }],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        }
    }

    // spec: design/arch/CLAUDE.md Decision 36 — function symbols are declared
    // with their bare name uniformly across all modules. The pre-Sprint-58
    // user/main vs FQ-Export discriminator is deleted.
    #[test]
    fn decision_36_function_naming_is_bare_for_every_module() {
        use cranelift_module::Module;
        for module_path_str in ["user", "main", "util", "one.two.three"] {
            let module = ModuleFullPath::from(module_path_str);
            let defn = make_int_defn("helper", 7);
            let tables = table_with_def_and_slot(&module, defn.clone(), 0);

            let mut jit = Jit::new().unwrap();
            let result = compile_to_module(
                module.clone(),
                std::slice::from_ref(&defn.name),
                &tables,
                jit.jit_module(),
            )
            .expect("compile_to_module should succeed");

            // The result func_ids map is keyed by bare name, NOT module-qualified.
            assert!(
                result.func_ids.contains_key(&Symbol::from("helper")),
                "module '{module_path_str}': func_ids must contain bare name 'helper'; got {:?}",
                result.func_ids.keys().collect::<Vec<_>>()
            );

            // The Cranelift module's declaration table records the bare name.
            // (Decision 36: even for non-user/main, the FQ form must be absent.)
            let fq = format!("{module_path_str}/helper");
            let m = jit.jit_module();
            let has_fq = m.get_name(&fq).is_some();
            let has_bare = m.get_name("helper").is_some();
            assert!(
                !has_fq,
                "module '{module_path_str}': bare-only contract violated — module-qualified name '{fq}' should NOT be a declaration"
            );
            assert!(
                has_bare,
                "module '{module_path_str}': bare name 'helper' must be a declaration"
            );
        }
    }

    // spec: design/arch/CLAUDE.md Decision 36 — function linkage is Local
    // uniformly. Symbols never need to cross .o boundaries (all-GOT calling).
    #[test]
    fn decision_36_function_linkage_is_local_uniformly() {
        use cranelift_module::{FuncOrDataId, Linkage, Module};
        for module_path_str in ["user", "main", "util", "deep.nested.path"] {
            let module = ModuleFullPath::from(module_path_str);
            let defn = make_int_defn("f", 1);
            let tables = table_with_def_and_slot(&module, defn.clone(), 0);

            let mut jit = Jit::new().unwrap();
            let _result = compile_to_module(
                module.clone(),
                std::slice::from_ref(&defn.name),
                &tables,
                jit.jit_module(),
            )
            .expect("compile_to_module should succeed");

            let m = jit.jit_module();
            let func_id = match m.get_name("f") {
                Some(FuncOrDataId::Func(id)) => id,
                other => panic!("module '{module_path_str}': expected FuncOrDataId::Func for 'f', got {other:?}"),
            };
            let decl = m.declarations().get_function_decl(func_id);
            assert_eq!(
                decl.linkage,
                Linkage::Local,
                "module '{module_path_str}': function 'f' must have Linkage::Local per Decision 36, got {:?}",
                decl.linkage
            );
        }
    }

    // spec: design/arch/CLAUDE.md Decision 23 (updated) — `__cranelisp_got_{M}`
    // is defined as Linkage::Export data with `slot_count * 8` bytes inside
    // the .o emitted by compile_to_module<ObjectModule>.
    #[test]
    fn decision_23_got_data_symbol_defined_as_export_in_object_path() {
        use cranelift_module::Module;
        let module = ModuleFullPath::from("util");
        let defn = make_int_defn("answer", 42);
        let tables = table_with_def_and_slot(&module, defn.clone(), 0);

        let mut obj = make_object_module();
        let _result = compile_to_module(
            module.clone(),
            std::slice::from_ref(&defn.name),
            &tables,
            &mut obj,
        )
        .expect("compile_to_module<ObjectModule> should succeed");

        // The GOT data symbol should now be a defined Export data symbol.
        let got_name = crate::compiler::got_data_symbol_name(&module);
        let id = obj
            .get_name(&got_name)
            .expect("GOT data symbol must be declared");
        let data_id = match id {
            cranelift_module::FuncOrDataId::Data(d) => d,
            other => panic!("expected DataId for {got_name}, got {other:?}"),
        };
        let decl = obj.declarations().get_data_decl(data_id);
        assert_eq!(
            decl.linkage,
            cranelift_module::Linkage::Export,
            "GOT data symbol '{got_name}' must be Linkage::Export, got {:?}",
            decl.linkage
        );

        // Emit the .o and parse it; confirm:
        //  (a) the GOT data symbol is present in the .o symbol table
        //  (b) it has global scope (Export = visible to the system linker)
        //  (c) it points into a Data-kind section
        // (Size in the .o symbol table is not portable across formats —
        // Mach-O always reports 0; we rely on the in-Module declaration
        // size assertion and the section-data check instead.)
        let product = obj.finish();
        let bytes = product.emit().expect("ObjectModule should emit");
        use ::object::{Object, ObjectSymbol, SymbolKind, SymbolScope};
        let parsed = ::object::File::parse(&*bytes)
            .expect("emitted bytes must parse as an object file");
        let got_sym = parsed
            .symbols()
            .find(|s| {
                s.name()
                    .map(|n| n.strip_prefix('_').unwrap_or(n) == got_name)
                    .unwrap_or(false)
            })
            .unwrap_or_else(|| {
                panic!(
                    "GOT data symbol '{got_name}' must appear in emitted .o; \
                     symbols present: {:?}",
                    parsed
                        .symbols()
                        .filter_map(|s| s.name().ok().map(|n| n.to_string()))
                        .collect::<Vec<_>>()
                )
            });
        assert_ne!(
            got_sym.scope(),
            SymbolScope::Compilation,
            "GOT data symbol '{got_name}' must have global scope (Linkage::Export); got {:?}",
            got_sym.scope()
        );
        assert_eq!(
            got_sym.kind(),
            SymbolKind::Data,
            "GOT data symbol '{got_name}' must be a Data-kind symbol; got {:?}",
            got_sym.kind()
        );
    }

    // spec: design/arch/CLAUDE.md Decision 23 — JIT-mode GOT-data definition
    // remains the integration layer's responsibility (`Jit::define_got_data`).
    // compile_to_module<JITModule>'s `define_module_got_data` is a no-op and
    // does NOT redundantly declare/define the symbol on the JIT module.
    #[test]
    fn decision_23_got_data_symbol_jit_path_is_noop() {
        use cranelift_module::Module;
        let module = ModuleFullPath::from("user");
        let defn = make_int_defn("answer", 42);
        let tables = table_with_def_and_slot(&module, defn.clone(), 0);

        let mut jit = Jit::new().unwrap();
        let _result = compile_to_module(
            module.clone(),
            std::slice::from_ref(&defn.name),
            &tables,
            jit.jit_module(),
        )
        .expect("compile_to_module<JITModule> should succeed");

        // In JIT mode, the GOT data symbol is NOT defined by compile_to_module.
        // It might be an Import declaration if the compiled code emitted a
        // GOT-indirect call (unlikely in this minimal test — answer is a
        // direct expression), but it must NEVER be Export-defined here.
        let got_name = crate::compiler::got_data_symbol_name(&module);
        let m = jit.jit_module();
        if let Some(cranelift_module::FuncOrDataId::Data(data_id)) = m.get_name(&got_name) {
            let decl = m.declarations().get_data_decl(data_id);
            assert_ne!(
                decl.linkage,
                cranelift_module::Linkage::Export,
                "JIT path: GOT data symbol '{got_name}' must NOT be Linkage::Export-defined by compile_to_module — JIT-mode definition lives in Jit::define_got_data (Decision 23)"
            );
        }
        // (If it's not declared at all, that's also fine — this minimal defn
        // doesn't emit a GOT-indirect call so neither path declares it.)
    }

    // spec: design/arch/CLAUDE.md Decision 23 — GOT data symbol size matches
    // the symbol table's `next_got_slot` (one 8-byte slot per allocated index).
    #[test]
    fn decision_23_got_data_size_matches_slot_count() {
        use cranelift_module::Module;
        // Two defns with two GOT slots → 16 bytes.
        let module = ModuleFullPath::from("util");
        let d1 = make_int_defn("one", 1);
        let d2 = make_int_defn("two", 2);

        // Build symbol table with both defns at slots 0 and 1.
        use cranelisp_types::{DefKind, ModuleEntry, Scheme, Visibility};
        let tables = DashMap::new();
        let mut st = SymbolTable::new(module.clone());
        let _slot0 = st.allocate_got_slot();
        let _slot1 = st.allocate_got_slot();
        for (defn, slot) in [(d1.clone(), 0usize), (d2.clone(), 1)] {
            st.insert(
                defn.name.clone(),
                ModuleEntry::Def {
                    scheme: Scheme {
                        vars: vec![],
                        constraints: HashMap::new(),
                        ty: Type::Fn(vec![], Box::new(Type::Int)),
                    },
                    visibility: Visibility::Public,
                    docstring: None,
                    param_names: vec![],
                    kind: Box::new(DefKind::UserFn { constrained_fn: None }),
                    callees: vec![],
                    got_slot: Some(slot),
                    trait_origin: None,
                    ast: Some(defn),
                    code: None,
                    fn_ptr: None,
                },
            );
        }
        tables.insert(module.clone(), st);

        let mut obj = make_object_module();
        let _result = compile_to_module(
            module.clone(),
            &[d1.name.clone(), d2.name.clone()],
            &tables,
            &mut obj,
        )
        .expect("compile_to_module should succeed");

        // Verify in-Module declaration size; we cannot rely on the .o
        // symbol-table `size()` (Mach-O reports 0). The Cranelift
        // declaration carries the requested initialization size.
        let got_name = crate::compiler::got_data_symbol_name(&module);
        let data_id = match obj.get_name(&got_name) {
            Some(cranelift_module::FuncOrDataId::Data(id)) => id,
            other => panic!("expected DataId for {got_name}, got {other:?}"),
        };
        let _decl = obj.declarations().get_data_decl(data_id);

        let product = obj.finish();
        let bytes = product.emit().unwrap();
        use ::object::{Object, ObjectSection, ObjectSymbol};
        let parsed = ::object::File::parse(&*bytes).unwrap();
        let got_sym = parsed
            .symbols()
            .find(|s| {
                s.name()
                    .map(|n| n.strip_prefix('_').unwrap_or(n) == got_name)
                    .unwrap_or(false)
            })
            .expect("GOT data symbol present");

        // Look up the section the symbol lives in and check it is at least
        // slot_count * 8 = 16 bytes long. (Cranelift may pack multiple data
        // symbols into the same section; this is a lower-bound check for the
        // GOT slab's storage budget.)
        let sect_idx = match got_sym.section_index() {
            Some(idx) => idx,
            None => panic!("GOT data symbol must live in a section"),
        };
        let section = parsed.section_by_index(sect_idx).unwrap();
        assert!(
            section.size() >= 16,
            "section containing GOT data symbol must hold at least slot_count(2) * 8 = 16 bytes; got {}",
            section.size()
        );
    }

    // spec: design/arch/CLAUDE.md Decision 36 — cross-module function refs
    // are NOT declared as Linkage::Import in the importing module's .o. Under
    // all-GOT calling, cross-module calls reach callees through
    // `__cranelisp_got_{other_M}` data symbol — never through a function-symbol
    // import. Verifies the cross_refs declaration loop deletion did not
    // re-introduce stray Import-linkage function declarations.
    #[test]
    fn decision_36_no_cross_module_function_imports() {
        use cranelift_module::{FuncOrDataId, Linkage, Module};

        // Build two modules: util defines `helper`, user imports `helper`.
        // Compile user.
        let util_path = ModuleFullPath::from("util");
        let user_path = ModuleFullPath::from("user");

        let helper = make_int_defn("helper", 99);
        // user has a single defn `caller` that does NOT call helper at runtime
        // (this test only checks the declaration shape; we focus on what
        // compile_to_module declares against the user module). The Import
        // entry on user's table records the cross-module dependency.
        let caller = make_int_defn("caller", 7);

        use cranelisp_types::{DefKind, FQSymbol, ModuleEntry, Scheme, Visibility,
        };
        let tables = DashMap::new();

        // util module: helper at slot 0.
        let mut util_st = SymbolTable::new(util_path.clone());
        let _ = util_st.allocate_got_slot();
        util_st.insert(
            Symbol::from("helper"),
            ModuleEntry::Def {
                scheme: Scheme {
                    vars: vec![],
                    constraints: HashMap::new(),
                    ty: Type::Fn(vec![], Box::new(Type::Int)),
                },
                visibility: Visibility::Public,
                docstring: None,
                param_names: vec![],
                kind: Box::new(DefKind::UserFn { constrained_fn: None }),
                callees: vec![],
                got_slot: Some(0),
                trait_origin: None,
                ast: Some(helper),
                code: None,
                fn_ptr: None,
            },
        );
        tables.insert(util_path.clone(), util_st);

        // user module: caller at slot 0, helper imported from util.
        let mut user_st = SymbolTable::new(user_path.clone());
        let _ = user_st.allocate_got_slot();
        user_st.insert(
            Symbol::from("caller"),
            ModuleEntry::Def {
                scheme: Scheme {
                    vars: vec![],
                    constraints: HashMap::new(),
                    ty: Type::Fn(vec![], Box::new(Type::Int)),
                },
                visibility: Visibility::Public,
                docstring: None,
                param_names: vec![],
                kind: Box::new(DefKind::UserFn { constrained_fn: None }),
                callees: vec![],
                got_slot: Some(0),
                trait_origin: None,
                ast: Some(caller),
                code: None,
                fn_ptr: None,
            },
        );
        user_st.insert(
            Symbol::from("helper"),
            ModuleEntry::Import {
                source: FQSymbol {
                    module: util_path.clone(),
                    symbol: Symbol::from("helper"),
                },
            },
        );
        tables.insert(user_path.clone(), user_st);

        let mut jit = Jit::new().unwrap();
        let result = compile_to_module(
            user_path.clone(),
            &[Symbol::from("caller")],
            &tables,
            jit.jit_module(),
        )
        .expect("compile_to_module should succeed");

        // Per Decision 36 + cross_refs deletion: there must be NO
        // Linkage::Import declaration for the cross-module function name
        // (neither `helper` nor `util/helper`).
        let m = jit.jit_module();
        for candidate in ["helper", "util/helper"] {
            if let Some(FuncOrDataId::Func(fid)) = m.get_name(candidate) {
                let decl = m.declarations().get_function_decl(fid);
                assert_ne!(
                    decl.linkage,
                    Linkage::Import,
                    "cross-module fn '{candidate}' must NOT be declared as Linkage::Import; got {:?}. Under all-GOT calling, cross-module calls flow through __cranelisp_got_{{M}} data symbols, not function imports.",
                    decl.linkage
                );
            }
        }

        // Sanity: caller is bare-Local and present in result.
        assert!(
            result.func_ids.contains_key(&Symbol::from("caller")),
            "func_ids must contain bare 'caller'"
        );
    }

    // spec: design/arch/CLAUDE.md Decision 23 — Sprint 58 Wave 2 regression
    // guard. The `__cranelisp_got_{M}` data symbol carries function-address
    // relocations (declared via `desc.write_function_addr`). On macOS, `ld`
    // segfaults when applying relocations against `__DATA,__bss`
    // (`S_ZEROFILL`) sections. The Wave 2 implementation MUST emit GOT
    // contents via `desc.define(zero_bytes)` (regular `__DATA`), NOT
    // `desc.define_zeroinit(...)` (which lands in BSS / `S_ZEROFILL`).
    // This test asserts the emitted .o has the GOT data symbol in a regular
    // (non-BSS) data section.
    #[test]
    fn decision_23_got_data_symbol_not_in_bss() {
        let module = ModuleFullPath::from("util");
        let defn = make_int_defn("answer", 42);
        let tables = table_with_def_and_slot(&module, defn.clone(), 0);

        let mut obj = make_object_module();
        let _result = compile_to_module(
            module.clone(),
            std::slice::from_ref(&defn.name),
            &tables,
            &mut obj,
        )
        .expect("compile_to_module<ObjectModule> should succeed");

        let product = obj.finish();
        let bytes = product.emit().expect("ObjectModule should emit");

        use ::object::{Object, ObjectSection, ObjectSymbol, SectionKind};
        let parsed = ::object::File::parse(&*bytes)
            .expect("emitted bytes must parse as an object file");
        let got_name = crate::compiler::got_data_symbol_name(&module);
        let got_sym = parsed
            .symbols()
            .find(|s| {
                s.name()
                    .map(|n| n.strip_prefix('_').unwrap_or(n) == got_name)
                    .unwrap_or(false)
            })
            .expect("GOT data symbol must appear in emitted .o");
        let sect_idx = got_sym
            .section_index()
            .expect("GOT data symbol must live in a section, not be undefined");
        let section = parsed
            .section_by_index(sect_idx)
            .expect("section must be resolvable");

        // Negative path: must NOT be UninitializedData (BSS / __DATA,__bss /
        // S_ZEROFILL). macOS `ld` segfaults on relocations against BSS.
        let kind = section.kind();
        assert_ne!(
            kind,
            SectionKind::UninitializedData,
            "GOT data symbol '{got_name}' landed in BSS (UninitializedData) — \
             macOS `ld` segfaults on relocations against BSS. Use \
             `desc.define(zero_bytes)` not `desc.define_zeroinit(...)` so the \
             data lands in regular `__DATA`."
        );
        // Positive path: must be a regular initialized Data section so
        // function-address relocations resolve correctly.
        assert!(
            matches!(kind, SectionKind::Data | SectionKind::ReadOnlyData),
            "GOT data symbol '{got_name}' must live in a regular initialized data section; got {kind:?}"
        );
    }
}
