// Cranelift ISA setup and JIT module lifecycle.
//
// Single ISA construction point. Addresses audit finding about
// multiple ISA constructions in the prototype.
//
// Ring 1: registers all runtime intrinsics by function pointer
// on the JITBuilder. Uses the naming convention from src/CLAUDE.md
// §"JIT Symbol Names".

use std::collections::HashMap;
use std::sync::{Arc, Mutex};

use cranelift::prelude::*;
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{FuncId, Linkage, Module};

use cranelisp_types::{
    CranelispError, DefKind, Defn, ErrorLocation, ModuleEntry, Span, Symbol, SymbolTables,
    got_data_symbol_name,
};

/// Register all runtime intrinsics on a JITBuilder by function pointer.
///
/// Reads `cranelisp_intrinsics::intrinsics_table()` — the published flat
/// Import-catalog (BC §4b invariant 11). Backend is a *reader* of this table,
/// not the owner: the per-record shape (`name`, `ptr`, `param_count`,
/// `has_return`, `is_runtime`) relocated to `cranelisp-intrinsics` at S76 W1a,
/// retiring the former in-crate `IntrinsicSymbol` + `intrinsic_symbols()`.
///
/// Each entry's `name`/`ptr` becomes a `JITBuilder::symbol(name, ptr)`
/// registration so backend-emitted `Linkage::Import` calls resolve at JIT
/// finalize. (The `.o`/`--link` path resolves the same names against the
/// `cranelisp-intrinsics` archive — see the catalog's `//!` for the ABI
/// guardrail.) Per Decision 0048 dep-ban, this catalog is intrinsics-only:
/// user-callable primitives reach codegen through the GOT-indirect path
/// against `PRIMITIVES_TABLE`, never through this enumeration.
fn register_intrinsics(builder: &mut JITBuilder) {
    for entry in cranelisp_intrinsics::intrinsics_table() {
        builder.symbol(entry.name, entry.ptr);
    }
}

/// Register every `PlatformEffect` primitive's jit-name → GOT-slot ptr on the
/// builder, walking each module's defs and following `Import` edges to the
/// defining table (BC §3 derivation 3, the third `Jit::new` step).
///
/// The symbol-table key IS the JIT linker name (`src/CLAUDE.md` §"JIT Symbol
/// Names"; the `jit_name` field was retired — `DefKind::PlatformEffect` has no
/// name payload). A platform effect contributes a symbol only when its GOT
/// slot is populated (a non-null pointer the platform DLL loader wrote at
/// registration). This mirrors int's former `collect_jit_setup` walk
/// (`worker.rs`), now absorbed behind the boundary; the GOT is the single
/// source of truth for the runtime address (Sprint 66 Wave 0 amendment).
fn register_platform_effect_symbols<C, L>(
    builder: &mut JITBuilder,
    symbol_tables: &SymbolTables<C, L>,
) where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    for table in symbol_tables.iter() {
        for (name, entry) in table.value().all_symbols() {
            match entry {
                // Direct def: a PlatformEffect with a populated slot in this
                // module's own GOT.
                ModuleEntry::Def { kind, .. }
                    if matches!(kind.as_ref(), DefKind::PlatformEffect { .. }) =>
                {
                    // The platform effect's GOT slot now rides on the
                    // `DefKind::PlatformEffect` variant (S83 reshape, FIXME 0358).
                    if let DefKind::PlatformEffect { got_slot, .. } = kind.as_ref() {
                        let ptr = table.value().got.load_slot(*got_slot);
                        if !ptr.is_null() {
                            builder.symbol(name.as_ref().to_string(), ptr);
                        }
                    }
                }
                // Imported def: follow the edge to the defining table and
                // register the platform fn from the source module's GOT.
                ModuleEntry::Import { source, .. } => {
                    if let Some(source_table) = symbol_tables.get(&source.module)
                        && let Some(ModuleEntry::Def { kind, .. }) =
                            source_table.get(source.symbol.as_ref())
                        && let DefKind::PlatformEffect { got_slot, .. } = kind.as_ref()
                    {
                        // The JIT linker name is the defining module's symbol
                        // key (the canonical jit-name), not the importing
                        // module's local alias — backend emits the `Import`
                        // against the source name. The slot rides on the
                        // `PlatformEffect` variant (S83 reshape, FIXME 0358).
                        let ptr = source_table.got.load_slot(*got_slot);
                        if !ptr.is_null() {
                            builder.symbol(source.symbol.as_ref().to_string(), ptr);
                        }
                    }
                }
                _ => {}
            }
        }
    }
}

/// Counter incremented once per `Jit::drop` that successfully calls
/// `unsafe JITModule::free_memory()`. Used by the unit tests below to
/// confirm the reclaim path executes; also available under
/// `CRANELISP_JIT_TRACE_RECLAIM=1` as a rough diagnostic.
///
/// Decision 31 requires the reclaim path actually runs on every `Jit` drop;
/// this counter is the observable evidence it does. Nothing in production
/// code reads it — it exists solely so tests can assert a side effect that
/// would otherwise be hidden inside Cranelift internals.
pub(crate) static JIT_FREE_MEMORY_CALL_COUNT: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);

/// Public read accessor for the `Jit::drop` reclaim counter. Lets the
/// integration layer's reclaim tests (Decision 31 Scenario 2 verification
/// in `src/code.rs::tests`) assert the underlying free path actually
/// fired without exposing the static directly.
pub fn jit_free_memory_call_count() -> u64 {
    JIT_FREE_MEMORY_CALL_COUNT.load(std::sync::atomic::Ordering::Relaxed)
}

/// JIT module wrapper. Owns the Cranelift JIT module and provides
/// function compilation and execution services.
///
/// # Memory reclaim (Decision 31)
///
/// The `module` field is wrapped in `Option<JITModule>` so that `Drop` can
/// `take()` it and call `unsafe JITModule::free_memory()`. Cranelift's default
/// `Memory::drop` intentionally `mem::forget`s every allocation (see
/// `cranelift-jit-0.116.1/src/memory.rs:269-276`), so reclaiming the mmap'd
/// executable pages requires the explicit `free_memory` call. The `Option`
/// is always `Some` during the `Jit`'s useful life and becomes `None` only
/// inside `Drop`, which is the last thing that happens.
///
/// # Safety invariant
///
/// `unsafe JITModule::free_memory()` is safe to call only when no function
/// pointer produced by this JIT is still reachable (`cranelift-jit-0.116.1/src/backend.rs:219`).
/// Ownership holders (`Arc<Jit>` cloned per-entry into `Code::Jit { jit, ptr }`
/// on each `ModuleEntry::Def.code` — Sprint 58 Wave 3b dissolved the
/// pre-existing `SharedState.kept_jits` side-store — or stack-local `Jit`
/// instances in REPL eval/backend tests) must ensure this before the last
/// handle drops. Per Decision 31 Scenario 2, when a REPL user redefines a
/// defn the prior entry's `Code::Jit` clone drops; once the last clone
/// referencing a particular `Jit` batch drops (no more entries reference
/// it), `Arc::drop` triggers `Jit::drop` which calls `free_memory` and
/// reclaims the per-batch JIT pages. Stack-local JIT paths run the
/// compiled function synchronously and drop the `Jit` only after that call
/// returns. See Decision 31 in `design/arch/CLAUDE.md` for the full
/// invariant and REPL-redefinition discussion.
///
// FIXME(W4/S77): several fields read only inside the now-`pub(crate)`
// JIT-orchestration methods, whose only production driver is int's parallel
// `pipeline.rs` path (out-of-crate). When S77 folds that path into the
// in-crate `compile_to_module`, these gain real in-crate readers and the
// allow is removed. The narrowing surfaces the dead-code as the expected
// signal (see `facades/backend.md` §Row 9).
#[allow(dead_code)]
pub struct Jit {
    /// Always `Some` during the JIT's useful life. `take()`n in `Drop` to
    /// invoke `unsafe free_memory()`.
    module: Option<JITModule>,
    ctx: cranelift::codegen::Context,
    func_ctx: FunctionBuilderContext,
    /// Host-promised symbol map — the escape hatch consulted at module
    /// finalization for symbols neither codegen-emitted, bundled
    /// (`cranelisp-primitives`), nor catalogued
    /// (`cranelisp_intrinsics::intrinsics_table()`).
    ///
    /// A Cranelift `symbol_lookup_fn` installed at construction reads this map
    /// (a clone of the `Arc` is moved into the closure); `define_symbol`
    /// inserts post-construction. So when an unresolved `Linkage::Import`
    /// relocation against `name` is settled at `finalize`, the lookup returns
    /// the host-promised pointer. The motivating member is the
    /// `DefKind::PrimitiveExtern` `discover-tests` body, promised by int at
    /// session init (test-discovery.md §6; BC §3 invariant 8).
    ///
    /// Pointers are stored as `usize` (not `*const u8`) so the map and the
    /// lookup closure are `Send` — the closure must be `Send` per the
    /// `JITBuilder::symbol_lookup_fn` bound; the conversion to `*const u8`
    /// happens inside the closure (`feedback_no_global_got`: this is not a GOT,
    /// it is the host-symbol escape hatch).
    host_symbols: Arc<Mutex<HashMap<String, usize>>>,
}

impl Drop for Jit {
    fn drop(&mut self) {
        if let Some(module) = self.module.take() {
            JIT_FREE_MEMORY_CALL_COUNT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            // SAFETY (Decision 31 / `cranelift-jit-0.116.1/src/backend.rs:219`):
            // `free_memory` requires that no fn pointer derived from this JIT
            // is called after this point. The invariant is upheld by the
            // owner of the `Jit` (typically `Arc<Jit>` cloned per-entry into
            // `Code::Jit { jit, ptr }` on `ModuleEntry::Def.code` — Sprint 58
            // Wave 3b dissolved the pre-existing `SharedState.kept_jits`
            // side-store — or a stack-local `Jit` whose compiled function
            // was already invoked synchronously). See the struct docs above
            // and Decision 31 in `design/arch/CLAUDE.md` for the full
            // argument.
            unsafe {
                module.free_memory();
            }
        }
    }
}

// FIXME(S77): the JIT-orchestration methods below narrowed to `pub(crate)`
// (S75 W3-follow, `facades/backend.md` §Row 9). Their only production caller is
// int's parallel `pipeline.rs` path (out-of-crate); in-crate they are reached
// only from unit tests. They gain in-crate readers when S77 folds the parallel
// path into `compile_to_module`. The allow holds the gate green while the
// narrowing signal stands. (W4 deleted the two methods that had NO in-crate
// caller at all: `build_shared_isa` + `declare_functions_prefixed`.)
#[allow(dead_code)]
impl Jit {
    /// Construct a JIT whose entire symbol set is derived from `symbol_tables`
    /// — the minimal JIT-setup boundary (BC §3).
    ///
    /// The caller (int) assembles nothing: before `JITModule::new`, this
    /// constructor derives the complete JIT symbol set from `symbol_tables`
    /// in three steps:
    ///
    ///   1. **Intrinsic Import targets** — every entry of
    ///      `cranelisp_intrinsics::intrinsics_table()` is registered via
    ///      `JITBuilder::symbol(name, ptr)` (the `register_intrinsics` step,
    ///      shared with the no-arg path).
    ///   2. **Per-module GOT data symbols** — one `__cranelisp_got_{M}` →
    ///      `symbol_tables[M].got.base_ptr()` symbol per module in
    ///      `symbol_tables` (incl. the synthetic `primitives` module), named
    ///      via the types-crate `got_data_symbol_name`. Decision 23: the
    ///      symbol address IS the slab base, no pointer-cell indirection.
    ///   3. **Platform-effect jit-names** — every `DefKind::PlatformEffect`
    ///      def with a populated GOT slot registers `(symbol-key,
    ///      got.load_slot(slot))`; `ModuleEntry::Import` edges are followed to
    ///      the defining table so an importing module's JIT resolves the
    ///      platform fn too. (The symbol-table key IS the JIT linker name per
    ///      `src/CLAUDE.md` §"JIT Symbol Names"; the retired `jit_name` field
    ///      no longer exists — `DefKind::PlatformEffect { scheduling_class }`.)
    ///
    /// `C`/`L` are the symbol-table carrier params; at int's JIT boundary the
    /// concrete type is `SymbolTables<Code, ()>`. The GOT base-ptr + platform
    /// jit-name walk read only `got` + `kind`/`got_slot`, so the body is
    /// `<C, L>`-blind (no `Code` knowledge — Principle 3 / Decision 0048
    /// dep-ban preserved: backend reaches primitives only through the
    /// type-erased mount).
    pub fn new<C, L>(symbol_tables: &SymbolTables<C, L>) -> Result<Self, CranelispError>
    where
        C: cranelisp_types::CodeStore,
        L: cranelisp_types::LinkerStore,
    {
        let isa = crate::cache::object::build_isa(false)?;
        let mut builder = JITBuilder::with_isa(isa, cranelift_module::default_libcall_names());

        // (1) Runtime + backend-emitted-call intrinsic Import targets.
        register_intrinsics(&mut builder);

        // (2) Per-module GOT data symbols — the symbol address IS the slab
        // base (Decision 23, no pointer-cell indirection).
        for entry in symbol_tables.iter() {
            let name = got_data_symbol_name(entry.key());
            builder.symbol(name, entry.value().got.base_ptr());
        }

        // (3) Platform-effect jit-names — walk defs + import chains.
        register_platform_effect_symbols(&mut builder, symbol_tables);

        Ok(Self::finish_builder(builder))
    }

    /// Create a new JIT instance with extra symbol registrations.
    ///
    /// Same as `new()` but pre-registers additional symbols on the
    /// JITBuilder before creating the module. This enables cross-module
    /// function calls (P4): when compiling module B that depends on
    /// module A, A's compiled function pointers are passed in as
    /// extra symbols so B can link against them.
    ///
    /// `pub(crate)` per design doc §1.4 — the boundary construct path is
    /// `Jit::new(symbol_tables)`. int's parallel hand-assembly path
    /// (`worker.rs`) is its only out-of-crate caller and is deleted in
    /// W-Collapse (S76 W2); the resulting dead-code on int's side is the
    /// expected narrowing signal.
    pub(crate) fn new_with_symbols(
        extra_symbols: &[(&str, *const u8)],
    ) -> Result<Self, CranelispError> {
        let isa = crate::cache::object::build_isa(false)?;
        Self::from_isa(isa, extra_symbols)
    }

    /// Create a new JIT instance using a pre-built ISA.
    ///
    /// Accepts extra symbol registrations, same as `new_with_symbols`.
    /// Construct the ISA once via the module-level `build_isa()`, then
    /// `Arc::clone` it for each worker's `Jit`.
    ///
    /// `pub(crate)` per design doc §1.4 — used internally if a shared-ISA
    /// micro-optimisation for per-symbol batches ever lands; no external
    /// caller (`feedback_callee_api_for_caller_only`).
    #[allow(dead_code)]
    pub(crate) fn new_with_isa(
        isa: Arc<dyn cranelift::codegen::isa::TargetIsa>,
        extra_symbols: &[(&str, *const u8)],
    ) -> Result<Self, CranelispError> {
        Self::from_isa(isa, extra_symbols)
    }

    /// Internal constructor: build a Jit from an ISA and extra symbols.
    fn from_isa(
        isa: Arc<dyn cranelift::codegen::isa::TargetIsa>,
        extra_symbols: &[(&str, *const u8)],
    ) -> Result<Self, CranelispError> {
        let mut builder = JITBuilder::with_isa(isa, cranelift_module::default_libcall_names());
        register_intrinsics(&mut builder);

        // Register extra symbols from previously compiled JIT modules.
        for &(name, ptr) in extra_symbols {
            builder.symbol(name, ptr);
        }

        Ok(Self::finish_builder(builder))
    }

    /// Finalise a fully-populated `JITBuilder` into a `Jit`.
    ///
    /// Shared tail of every construct path (`new`, `from_isa`): installs the
    /// host-symbol escape-hatch `symbol_lookup_fn` over a fresh shared map,
    /// builds the `JITModule`, makes the codegen context, and zeroes the 6
    /// convenience intrinsic-FuncId fields (populated later by
    /// `declare_intrinsics` during the per-call compile). The caller is
    /// responsible for having registered all eager symbols on `builder` first;
    /// the lookup fn is the lazy, consulted-at-finalize tail that lets
    /// `define_symbol` settle host-promised externs added post-construction.
    fn finish_builder(mut builder: JITBuilder) -> Self {
        // The host-symbol escape hatch (BC §3 invariant 8). The lookup closure
        // is consulted by Cranelift at module finalization for any unresolved
        // `Linkage::Import` relocation not already satisfied by an eager
        // `JITBuilder::symbol`. It reads the shared map; `define_symbol`
        // inserts into the same `Arc` post-construction.
        let host_symbols: Arc<Mutex<HashMap<String, usize>>> = Arc::new(Mutex::new(HashMap::new()));
        {
            let lookup = Arc::clone(&host_symbols);
            builder.symbol_lookup_fn(Box::new(move |name: &str| {
                lookup
                    .lock()
                    .unwrap_or_else(|p| p.into_inner())
                    .get(name)
                    .map(|&addr| addr as *const u8)
            }));
        }

        let module = JITModule::new(builder);

        let ctx = module.make_context();
        let func_ctx = FunctionBuilderContext::new();

        Jit {
            module: Some(module),
            ctx,
            func_ctx,
            host_symbols,
        }
    }

    /// Promise a host symbol's body post-construction — the additive
    /// host-symbol escape hatch (test-discovery.md §6; BC §3 invariant 8).
    ///
    /// Inserts `(name → ptr)` into the map the JIT's `symbol_lookup_fn`
    /// consults at module finalization. When an unresolved `Linkage::Import`
    /// relocation against `name` is settled, the lookup returns `ptr`. This is
    /// the documented escape hatch for host-promised symbols whose body is
    /// neither codegen-emitted, bundled (`cranelisp-primitives`), nor
    /// catalogued (`cranelisp_intrinsics::intrinsics_table()`). The motivating
    /// member is `discover-tests` (a `DefKind::PrimitiveExtern` whose body
    /// reads int's live session state — Principle 18 / Decision 0048 keep that
    /// body out of `cranelisp-intrinsics`); int calls this at session init.
    ///
    /// Additive only — no forked constructor (Principle 11), no callback
    /// indirection, no registry. `Jit::new`'s derived-from-`symbol_tables`
    /// eager registration stands as the default; this only adds host promises
    /// on top.
    ///
    /// # Safety
    ///
    /// `ptr` must point to a function whose ABI matches the call shape backend
    /// emits for the extern (an `extern "C"` callable with the entry's arity
    /// and an `i64` return). It must remain valid for the lifetime of every
    /// function compiled by this JIT that references `name`. The caller (int)
    /// guarantees this by promising a `'static` host fn pointer.
    pub fn define_symbol(&self, name: &str, ptr: *const u8) {
        self.host_symbols
            .lock()
            .unwrap_or_else(|p| p.into_inner())
            .insert(name.to_string(), ptr as usize);
    }

    /// Access the inner `JITModule` by shared reference.
    ///
    /// Panics (via `unreachable!`) only if called after `Drop::drop` has taken
    /// the module, which cannot happen through the normal API: `&self` cannot
    /// coexist with `drop`.
    #[inline]
    fn module(&self) -> &JITModule {
        self.module.as_ref().unwrap_or_else(|| {
            unreachable!(
                "invariant: Jit::module is Some for the Jit's entire lifetime; \
                 only Drop::drop moves it out, and &self cannot outlive Drop"
            )
        })
    }

    /// Access the inner `JITModule` by mutable reference.
    #[inline]
    fn module_mut(&mut self) -> &mut JITModule {
        self.module.as_mut().unwrap_or_else(|| {
            unreachable!(
                "invariant: Jit::module is Some for the Jit's entire lifetime; \
                 only Drop::drop moves it out, and &mut self cannot outlive Drop"
            )
        })
    }

    /// Declare runtime intrinsics as imported functions in the JIT module.
    ///
    /// Must be called before compiling any function that needs heap operations.
    /// Returns the declared FuncIds for use by codegen.
    ///
    /// Delegates to the generic `declare_intrinsics_generic<M>` and projects out
    /// the 6 convenience FuncIds callers use directly.
    pub(crate) fn declare_intrinsics(&mut self) -> Result<IntrinsicIds, CranelispError> {
        let generic_ids = declare_intrinsics_generic(self.module_mut())?;

        Ok(IntrinsicIds {
            alloc: generic_ids.alloc.expect("runtime/alloc must be declared"),
            dealloc: generic_ids
                .dealloc
                .expect("runtime/dealloc must be declared"),
            alloc_string: generic_ids
                .alloc_string
                .expect("runtime/alloc_string must be declared"),
            panic: generic_ids.panic.expect("runtime/panic must be declared"),
            vec_new: generic_ids
                .vec_new
                .expect("runtime/vec_new must be declared"),
            vec_drop: generic_ids
                .vec_drop
                .expect("runtime/vec_drop must be declared"),
        })
    }

    /// Declare all functions in the JIT module, returning a name->FuncId map.
    /// Used in Batch mode so functions can reference each other.
    pub(crate) fn declare_functions(
        &mut self,
        defns: &[&Defn],
    ) -> Result<HashMap<Symbol, FuncId>, CranelispError> {
        let mut func_ids = HashMap::new();
        for defn in defns {
            let sig = self.build_sig(defn.params().len());
            let func_id = self
                .module_mut()
                .declare_function(&defn.name, Linkage::Export, &sig)
                .map_err(|e| CranelispError::CodegenError {
                    message: format!("failed to declare function '{}': {e}", defn.name),
                    location: ErrorLocation::from_span(defn.span),
                })?;
            func_ids.insert(defn.name.clone(), func_id);
        }
        Ok(func_ids)
    }

    /// Declare imported functions in the JIT module for cross-module linking.
    ///
    /// In Batch mode, when a module calls functions from other modules, those
    /// functions must be declared with `Linkage::Import` so that Cranelift's
    /// linker can resolve the cross-references. The orchestrator compiles
    /// modules in dependency order, so imported functions are already finalized
    /// by the time the calling module is compiled.
    ///
    /// Each entry is `(name, param_count)`. Returns the declared FuncIds merged
    /// into the provided `func_ids` map.
    pub(crate) fn declare_imported_functions(
        &mut self,
        imports: &[(Symbol, usize)],
        func_ids: &mut HashMap<Symbol, FuncId>,
    ) -> Result<(), CranelispError> {
        for (name, param_count) in imports {
            let sig = self.build_sig(*param_count);
            let func_id = self
                .module_mut()
                .declare_function(name, Linkage::Import, &sig)
                .map_err(|e| CranelispError::CodegenError {
                    message: format!("failed to declare imported function '{}': {e}", name),
                    location: ErrorLocation::from_span(Span::SYNTHETIC),
                })?;
            func_ids.insert(name.clone(), func_id);
        }
        Ok(())
    }

    // Decision 23 (Sprint 58 Wave 2 follow-on): per-module GOT slabs are
    // registered with the JIT via `JITBuilder::symbol()` (passed through
    // `Jit::new_with_symbols`'s `extra_symbols`). The symbol address IS the
    // slab base (`GotTable.base_ptr()`) — no extra pointer-cell indirection.
    // The matching `apply.rs` CLIF declares the symbol as `Linkage::Import`
    // data on demand and resolves it via `global_value`. This matches
    // object-mode's `define_module_got_data` shape so the same CLIF runs
    // byte-identically in both modes. The previous helper that defined an
    // 8-byte data block containing the slab pointer (an extra indirection)
    // has been removed; callers now fold GOT registrations into
    // `extra_symbols`.

    /// Finalize all pending function definitions.
    pub(crate) fn finalize(&mut self) -> Result<(), CranelispError> {
        self.module_mut()
            .finalize_definitions()
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to finalize JIT definitions: {e}"),
                location: ErrorLocation::from_span(Span::SYNTHETIC),
            })
    }

    /// Get the finalized code pointer for a function by FuncId.
    pub(crate) fn get_finalized_ptr(&self, func_id: FuncId) -> *const u8 {
        self.module().get_finalized_function(func_id)
    }

    /// Finalize definitions and return the code pointer for a named function.
    /// Convenience method that looks up the FuncId by name (re-declaring with
    /// the same param count).
    pub(crate) fn finalize_and_get_ptr(
        &mut self,
        name: &Symbol,
        param_count: usize,
    ) -> Result<*const u8, CranelispError> {
        self.finalize()?;

        // Re-declare with same signature to get the existing FuncId.
        let sig = self.build_sig(param_count);
        let func_id = self
            .module_mut()
            .declare_function(name, Linkage::Export, &sig)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to look up function '{}': {e}", name),
                location: ErrorLocation::from_span(Span::SYNTHETIC),
            })?;

        Ok(self.module().get_finalized_function(func_id))
    }

    /// Look up a finalized function pointer by name and param count.
    ///
    /// Must be called after `finalize()`. Re-declares the function with
    /// the same signature to obtain the FuncId, then returns the code pointer.
    pub(crate) fn get_ptr_by_name(
        &mut self,
        name: &Symbol,
        param_count: usize,
    ) -> Result<*const u8, CranelispError> {
        let sig = self.build_sig(param_count);
        let func_id = self
            .module_mut()
            .declare_function(name, Linkage::Export, &sig)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to look up function '{}': {e}", name),
                location: ErrorLocation::from_span(Span::SYNTHETIC),
            })?;
        Ok(self.module().get_finalized_function(func_id))
    }

    /// Get a mutable reference to the inner JIT module.
    /// Needed by FnCompiler for declaring extern functions.
    pub fn jit_module(&mut self) -> &mut JITModule {
        self.module_mut()
    }

    /// Build a Cranelift function signature: all params and return are i64.
    fn build_sig(&self, param_count: usize) -> cranelift::codegen::ir::Signature {
        let mut sig = self.module().make_signature();
        for _ in 0..param_count {
            sig.params.push(AbiParam::new(types::I64));
        }
        sig.returns.push(AbiParam::new(types::I64));
        sig
    }
}

/// FuncIds for declared runtime intrinsics.
///
/// Internal (`pub(crate)`) per the S75 W3-follow narrowing
/// (`facades/backend.md` §"`jit` shape DTOs (Row 15)") — returned from the
/// now-`pub(crate)` `Jit::declare_intrinsics`.
///
// FIXME(W4/S77): constructed/read only by the now-`pub(crate)`
// `Jit::declare_intrinsics` whose production caller is int's parallel
// `pipeline.rs` path (out-of-crate). Allow holds the gate; W4/S77 folds.
#[allow(dead_code)]
pub(crate) struct IntrinsicIds {
    pub alloc: FuncId,
    pub dealloc: FuncId,
    pub alloc_string: FuncId,
    pub panic: FuncId,
    pub vec_new: FuncId,
    pub vec_drop: FuncId,
}

/// FuncIds for all intrinsic functions, populated during declare_intrinsics.
///
/// Replaces the scattered approach where intrinsic FuncIds are stored on
/// individual Jit fields and ad-hoc lookup maps. This is the single
/// source of truth for intrinsic function IDs across all module types.
///
/// Internal (`pub(crate)`) per the S75 W3-follow narrowing
/// (`facades/backend.md` §"`jit` shape DTOs (Row 15)") — returned from the
/// now-`pub(crate)` `declare_intrinsics_generic`.
#[derive(Default)]
pub(crate) struct IntrinsicFuncIds {
    /// All intrinsics indexed by JIT symbol name.
    pub by_name: HashMap<Symbol, FuncId>,
    // Convenience accessors for commonly-used intrinsics (used directly by FnCompiler).
    pub alloc: Option<FuncId>,
    pub dealloc: Option<FuncId>,
    pub alloc_string: Option<FuncId>,
    pub panic: Option<FuncId>,
    pub vec_new: Option<FuncId>,
    pub vec_drop: Option<FuncId>,
}

/// Declare all runtime and primitive intrinsics in a Cranelift module.
///
/// For JITModule: these resolve to function pointers registered via JITBuilder::symbol().
/// For ObjectModule: these become Import symbols resolved by the linker.
///
/// This is the unified intrinsic declaration path. Both `Jit::declare_intrinsics`
/// and the object path's `declare_intrinsic_imports` delegate to this function.
pub(crate) fn declare_intrinsics_generic<M: Module>(
    module: &mut M,
) -> Result<IntrinsicFuncIds, CranelispError> {
    let mut ids = IntrinsicFuncIds::default();

    for entry in cranelisp_intrinsics::intrinsics_table() {
        let mut sig = module.make_signature();
        for _ in 0..entry.param_count {
            sig.params.push(AbiParam::new(types::I64));
        }
        if entry.has_return {
            sig.returns.push(AbiParam::new(types::I64));
        }

        let func_id = module
            .declare_function(entry.name, Linkage::Import, &sig)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare intrinsic '{}': {e}", entry.name),
                location: ErrorLocation::from_span(Span::SYNTHETIC),
            })?;

        ids.by_name.insert(Symbol::from(entry.name), func_id);

        // Set convenience accessors for the 6 special intrinsics.
        match entry.name {
            "runtime/alloc" => ids.alloc = Some(func_id),
            "runtime/dealloc" => ids.dealloc = Some(func_id),
            "runtime/alloc_string" => ids.alloc_string = Some(func_id),
            "runtime/panic" => ids.panic = Some(func_id),
            "runtime/vec_new" => ids.vec_new = Some(func_id),
            "runtime/vec_drop" => ids.vec_drop = Some(func_id),
            _ => {}
        }
    }

    Ok(ids)
}

#[cfg(test)]
mod tests;

#[cfg(test)]
mod disasm_tests;
