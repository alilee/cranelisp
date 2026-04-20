// Cranelift ISA setup and JIT module lifecycle.
//
// Single ISA construction point. Addresses audit finding about
// multiple ISA constructions in the prototype.
//
// Ring 1: registers all runtime intrinsics by function pointer
// on the JITBuilder. Uses the naming convention from src/CLAUDE.md
// §"JIT Symbol Names".

use std::collections::HashMap;
use std::sync::Arc;

use cranelift::prelude::*;
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{FuncId, Linkage, Module};

use cranelisp_types::{
    CranelispError, Defn, Span, Symbol,
};

/// Compilation artifacts returned by `compile_defn`.
pub struct CompileArtifacts {
    /// Cranelift IR text (captured before machine code generation).
    pub clif_ir: String,
    /// Native disassembly text (None if disasm not supported on this platform).
    pub disasm: Option<String>,
    /// Size of generated machine code in bytes.
    pub code_size: Option<usize>,
}

use crate::compiler::{CompileContext, FnCompiler};

/// Build the ISA for the current host architecture.
///
/// Single construction point for the entire backend.
pub fn build_isa() -> Result<Arc<dyn cranelift::codegen::isa::TargetIsa>, CranelispError> {
    let mut flag_builder = settings::builder();
    flag_builder
        .set("use_colocated_libcalls", "false")
        .map_err(|e| CranelispError::CodegenError {
            message: format!("failed to set ISA flag: {e}"),
            span: Span::SYNTHETIC,
        })?;
    flag_builder
        .set("is_pic", "false")
        .map_err(|e| CranelispError::CodegenError {
            message: format!("failed to set ISA flag: {e}"),
            span: Span::SYNTHETIC,
        })?;

    let isa_builder =
        cranelift_native::builder().map_err(|msg| CranelispError::CodegenError {
            message: format!("host architecture not supported: {msg}"),
            span: Span::SYNTHETIC,
        })?;

    isa_builder
        .finish(settings::Flags::new(flag_builder))
        .map_err(|e| CranelispError::CodegenError {
            message: format!("failed to build ISA: {e}"),
            span: Span::SYNTHETIC,
        })
}

/// Intrinsic symbol descriptor: JIT name, function pointer, and param count.
///
/// This is the authoritative list of runtime and primitive intrinsics.
/// All consumers (JIT builder, Linker, IntrinsicTable) derive from this.
pub struct IntrinsicSymbol {
    /// JIT symbol name (e.g., "runtime/alloc", "str-concat").
    pub name: &'static str,
    /// Function pointer to the Rust implementation.
    pub ptr: *const u8,
    /// Number of parameters.
    pub param_count: usize,
    /// Whether this is a runtime-internal function (true) or user-visible primitive (false).
    pub is_runtime: bool,
    /// Whether the function returns an i64 value (false = void).
    pub has_return: bool,
}

/// Return the authoritative list of all runtime and primitive intrinsic symbols.
///
/// Single source of truth for the JIT name -> function pointer mapping.
/// Addresses cache audit HIGH-1: one authoritative registry for JIT,
/// Linker, and ObjectModule paths.
///
/// Convention: runtime infrastructure uses `runtime/name` prefix.
/// User-visible primitives use spec kebab-case names.
pub fn intrinsic_symbols() -> Vec<IntrinsicSymbol> {
    vec![
        // Runtime infrastructure (internal, not user-callable)
        IntrinsicSymbol { name: "runtime/alloc", ptr: cranelisp_runtime::heap_alloc as *const u8, param_count: 1, is_runtime: true, has_return: true },
        IntrinsicSymbol { name: "runtime/dealloc", ptr: cranelisp_runtime::heap_dealloc as *const u8, param_count: 1, is_runtime: true, has_return: true },
        IntrinsicSymbol { name: "runtime/panic", ptr: cranelisp_runtime::runtime_panic as *const u8, param_count: 2, is_runtime: true, has_return: true },
        IntrinsicSymbol { name: "runtime/rc_underflow_check", ptr: cranelisp_runtime::rc_underflow_check as *const u8, param_count: 1, is_runtime: true, has_return: true },
        IntrinsicSymbol { name: "runtime/alloc_string", ptr: cranelisp_runtime::heap_alloc_string as *const u8, param_count: 2, is_runtime: true, has_return: true },
        IntrinsicSymbol { name: "runtime/string_read", ptr: cranelisp_runtime::string_read as *const u8, param_count: 1, is_runtime: true, has_return: true },
        IntrinsicSymbol { name: "runtime/vec_new", ptr: cranelisp_runtime::vec_new as *const u8, param_count: 1, is_runtime: true, has_return: true },
        IntrinsicSymbol { name: "runtime/vec_drop", ptr: cranelisp_runtime::vec_drop as *const u8, param_count: 2, is_runtime: true, has_return: false },
        IntrinsicSymbol { name: "runtime/run_io", ptr: cranelisp_runtime::cranelisp_run_io as *const u8, param_count: 1, is_runtime: true, has_return: true },
        // IVar intrinsics for lenient evaluation
        IntrinsicSymbol { name: "cranelisp_ivar_create", ptr: cranelisp_runtime::ivar_create as *const u8, param_count: 1, is_runtime: true, has_return: true },
        IntrinsicSymbol { name: "cranelisp_ivar_spark", ptr: cranelisp_runtime::ivar_spark as *const u8, param_count: 1, is_runtime: true, has_return: true },
        IntrinsicSymbol { name: "cranelisp_ivar_force", ptr: cranelisp_runtime::ivar_force as *const u8, param_count: 1, is_runtime: true, has_return: true },
        // Trace runtime symbols
        IntrinsicSymbol { name: "cranelisp_trace_enter", ptr: cranelisp_runtime::cranelisp_trace_enter as *const u8, param_count: 4, is_runtime: true, has_return: false },
        IntrinsicSymbol { name: "cranelisp_trace_exit", ptr: cranelisp_runtime::cranelisp_trace_exit as *const u8, param_count: 2, is_runtime: true, has_return: true },
        IntrinsicSymbol { name: "cranelisp_trace_swap_got", ptr: cranelisp_runtime::cranelisp_trace_swap_got as *const u8, param_count: 4, is_runtime: true, has_return: true },
        IntrinsicSymbol { name: "cranelisp_trace_restore_got", ptr: cranelisp_runtime::cranelisp_trace_restore_got as *const u8, param_count: 2, is_runtime: true, has_return: false },
        IntrinsicSymbol { name: "cranelisp_collect_trace", ptr: cranelisp_runtime::cranelisp_collect_trace as *const u8, param_count: 0, is_runtime: true, has_return: true },
        IntrinsicSymbol { name: "cranelisp_trace_first_child_nanos", ptr: cranelisp_runtime::cranelisp_trace_first_child_nanos as *const u8, param_count: 1, is_runtime: true, has_return: true },
        IntrinsicSymbol { name: "cranelisp_trace_format", ptr: cranelisp_runtime::cranelisp_trace_format as *const u8, param_count: 2, is_runtime: true, has_return: true },
        // Trace ADT field accessors
        IntrinsicSymbol { name: "cranelisp_trace_name", ptr: cranelisp_runtime::cranelisp_trace_name as *const u8, param_count: 1, is_runtime: true, has_return: true },
        IntrinsicSymbol { name: "cranelisp_trace_params", ptr: cranelisp_runtime::cranelisp_trace_params as *const u8, param_count: 1, is_runtime: true, has_return: true },
        IntrinsicSymbol { name: "cranelisp_trace_result", ptr: cranelisp_runtime::cranelisp_trace_result as *const u8, param_count: 1, is_runtime: true, has_return: true },
        IntrinsicSymbol { name: "cranelisp_trace_children", ptr: cranelisp_runtime::cranelisp_trace_children as *const u8, param_count: 1, is_runtime: true, has_return: true },
        IntrinsicSymbol { name: "cranelisp_trace_nanos", ptr: cranelisp_runtime::cranelisp_trace_nanos as *const u8, param_count: 1, is_runtime: true, has_return: true },
        // Vec extern primitives (user-visible and internal)
        IntrinsicSymbol { name: "vec-len", ptr: cranelisp_runtime::vec_len as *const u8, param_count: 1, is_runtime: false, has_return: true },
        IntrinsicSymbol { name: "vec-set-copy", ptr: cranelisp_runtime::vec_set_copy as *const u8, param_count: 4, is_runtime: false, has_return: true },
        IntrinsicSymbol { name: "vec-push-copy", ptr: cranelisp_runtime::vec_push_copy as *const u8, param_count: 3, is_runtime: false, has_return: true },
        IntrinsicSymbol { name: "vec-push-grow", ptr: cranelisp_runtime::vec_push_grow as *const u8, param_count: 2, is_runtime: false, has_return: true },
        // Extern primitives (user-visible via primitives module)
        IntrinsicSymbol { name: "str-concat", ptr: cranelisp_runtime::str_concat as *const u8, param_count: 2, is_runtime: false, has_return: true },
        IntrinsicSymbol { name: "str-eq", ptr: cranelisp_runtime::str_eq as *const u8, param_count: 2, is_runtime: false, has_return: true },
        IntrinsicSymbol { name: "str-len", ptr: cranelisp_runtime::str_len as *const u8, param_count: 1, is_runtime: false, has_return: true },
        IntrinsicSymbol { name: "string-identity", ptr: cranelisp_runtime::string_identity as *const u8, param_count: 1, is_runtime: false, has_return: true },
        IntrinsicSymbol { name: "int-to-string", ptr: cranelisp_runtime::int_to_string as *const u8, param_count: 1, is_runtime: false, has_return: true },
        IntrinsicSymbol { name: "float-to-string", ptr: cranelisp_runtime::float_to_string as *const u8, param_count: 1, is_runtime: false, has_return: true },
        IntrinsicSymbol { name: "bool-to-string", ptr: cranelisp_runtime::bool_to_string as *const u8, param_count: 1, is_runtime: false, has_return: true },
        IntrinsicSymbol { name: "parse-int", ptr: cranelisp_runtime::parse_int as *const u8, param_count: 1, is_runtime: false, has_return: true },
        // Extended string primitives
        IntrinsicSymbol { name: "substring", ptr: cranelisp_runtime::str_substring as *const u8, param_count: 3, is_runtime: false, has_return: true },
        IntrinsicSymbol { name: "char-at", ptr: cranelisp_runtime::str_char_at as *const u8, param_count: 2, is_runtime: false, has_return: true },
        IntrinsicSymbol { name: "split", ptr: cranelisp_runtime::str_split as *const u8, param_count: 2, is_runtime: false, has_return: true },
        IntrinsicSymbol { name: "join", ptr: cranelisp_runtime::str_join as *const u8, param_count: 2, is_runtime: false, has_return: true },
        IntrinsicSymbol { name: "replace", ptr: cranelisp_runtime::str_replace as *const u8, param_count: 3, is_runtime: false, has_return: true },
        IntrinsicSymbol { name: "trim", ptr: cranelisp_runtime::str_trim as *const u8, param_count: 1, is_runtime: false, has_return: true },
        IntrinsicSymbol { name: "starts-with?", ptr: cranelisp_runtime::str_starts_with as *const u8, param_count: 2, is_runtime: false, has_return: true },
        IntrinsicSymbol { name: "ends-with?", ptr: cranelisp_runtime::str_ends_with as *const u8, param_count: 2, is_runtime: false, has_return: true },
        IntrinsicSymbol { name: "contains?", ptr: cranelisp_runtime::str_contains as *const u8, param_count: 2, is_runtime: false, has_return: true },
        IntrinsicSymbol { name: "to-upper", ptr: cranelisp_runtime::str_to_upper as *const u8, param_count: 1, is_runtime: false, has_return: true },
        IntrinsicSymbol { name: "to-lower", ptr: cranelisp_runtime::str_to_lower as *const u8, param_count: 1, is_runtime: false, has_return: true },
        // Marshal primitives (macros module + primitives module)
        IntrinsicSymbol { name: "sconcat", ptr: cranelisp_runtime::sconcat as *const u8, param_count: 2, is_runtime: false, has_return: true },
        IntrinsicSymbol { name: "quote-sexp", ptr: cranelisp_runtime::quote_sexp as *const u8, param_count: 1, is_runtime: false, has_return: true },
        // Operator wrapper functions (for trait methods as first-class values, spec §7.6)
        IntrinsicSymbol { name: "cranelisp_op_add", ptr: cranelisp_runtime::cranelisp_op_add as *const u8, param_count: 2, is_runtime: true, has_return: true },
        IntrinsicSymbol { name: "cranelisp_op_sub", ptr: cranelisp_runtime::cranelisp_op_sub as *const u8, param_count: 2, is_runtime: true, has_return: true },
        IntrinsicSymbol { name: "cranelisp_op_mul", ptr: cranelisp_runtime::cranelisp_op_mul as *const u8, param_count: 2, is_runtime: true, has_return: true },
        IntrinsicSymbol { name: "cranelisp_op_div", ptr: cranelisp_runtime::cranelisp_op_div as *const u8, param_count: 2, is_runtime: true, has_return: true },
        IntrinsicSymbol { name: "cranelisp_op_eq", ptr: cranelisp_runtime::cranelisp_op_eq as *const u8, param_count: 2, is_runtime: true, has_return: true },
        IntrinsicSymbol { name: "cranelisp_op_neq", ptr: cranelisp_runtime::cranelisp_op_neq as *const u8, param_count: 2, is_runtime: true, has_return: true },
        IntrinsicSymbol { name: "cranelisp_op_lt", ptr: cranelisp_runtime::cranelisp_op_lt as *const u8, param_count: 2, is_runtime: true, has_return: true },
        IntrinsicSymbol { name: "cranelisp_op_gt", ptr: cranelisp_runtime::cranelisp_op_gt as *const u8, param_count: 2, is_runtime: true, has_return: true },
        IntrinsicSymbol { name: "cranelisp_op_le", ptr: cranelisp_runtime::cranelisp_op_le as *const u8, param_count: 2, is_runtime: true, has_return: true },
        IntrinsicSymbol { name: "cranelisp_op_ge", ptr: cranelisp_runtime::cranelisp_op_ge as *const u8, param_count: 2, is_runtime: true, has_return: true },
    ]
}

/// Register all runtime intrinsics on a JITBuilder by function pointer.
///
/// Delegates to `intrinsic_symbols()` — the single source of truth.
fn register_intrinsics(builder: &mut JITBuilder) {
    for sym in intrinsic_symbols() {
        builder.symbol(sym.name, sym.ptr);
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
pub struct Jit {
    /// Always `Some` during the JIT's useful life. `take()`n in `Drop` to
    /// invoke `unsafe free_memory()`.
    module: Option<JITModule>,
    ctx: cranelift::codegen::Context,
    func_ctx: FunctionBuilderContext,
    /// FuncId for `runtime/alloc` — needed by heap emission helpers.
    alloc_func_id: Option<FuncId>,
    /// FuncId for `runtime/dealloc` — needed by RC dec emission.
    dealloc_func_id: Option<FuncId>,
    /// FuncId for `runtime/alloc_string` — needed by string literal codegen.
    alloc_string_func_id: Option<FuncId>,
    /// FuncId for `runtime/panic` — needed for match exhaustiveness failure.
    panic_func_id: Option<FuncId>,
    /// FuncId for `runtime/vec_new` — needed by Vec literal codegen.
    vec_new_func_id: Option<FuncId>,
    /// FuncId for `runtime/vec_drop` — needed by Vec drop glue.
    vec_drop_func_id: Option<FuncId>,
}

impl Drop for Jit {
    fn drop(&mut self) {
        if let Some(module) = self.module.take() {
            JIT_FREE_MEMORY_CALL_COUNT
                .fetch_add(1, std::sync::atomic::Ordering::Relaxed);
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

impl Jit {
    /// Create a new JIT instance for the current host architecture.
    pub fn new() -> Result<Self, CranelispError> {
        Self::new_with_symbols(&[])
    }

    /// Create a new JIT instance with extra symbol registrations.
    ///
    /// Same as `new()` but pre-registers additional symbols on the
    /// JITBuilder before creating the module. This enables cross-module
    /// function calls (P4): when compiling module B that depends on
    /// module A, A's compiled function pointers are passed in as
    /// extra symbols so B can link against them.
    pub fn new_with_symbols(
        extra_symbols: &[(&str, *const u8)],
    ) -> Result<Self, CranelispError> {
        let isa = build_isa()?;
        Self::from_isa(isa, extra_symbols)
    }

    /// Build a shared ISA for the current host architecture.
    ///
    /// Returns an `Arc<dyn TargetIsa>` that can be cloned and passed to
    /// multiple `Jit` instances via `new_with_isa()`. This avoids
    /// re-probing CPU features when creating many JIT instances (e.g.,
    /// one per codegen worker in N-core parallel compilation).
    pub fn build_shared_isa() -> Result<Arc<dyn cranelift::codegen::isa::TargetIsa>, CranelispError> {
        build_isa()
    }

    /// Create a new JIT instance using a pre-built ISA.
    ///
    /// Accepts extra symbol registrations, same as `new_with_symbols`.
    /// Use `Jit::build_shared_isa()` to construct the ISA once, then
    /// `Arc::clone` it for each worker's `Jit`.
    pub fn new_with_isa(
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

        let module = JITModule::new(builder);

        let ctx = module.make_context();
        let func_ctx = FunctionBuilderContext::new();

        Ok(Jit {
            module: Some(module),
            ctx,
            func_ctx,
            alloc_func_id: None,
            dealloc_func_id: None,
            alloc_string_func_id: None,
            panic_func_id: None,
            vec_new_func_id: None,
            vec_drop_func_id: None,
        })
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
    /// Delegates to the generic `declare_intrinsics_generic<M>` and stores
    /// the 6 convenience FuncIds on the Jit struct for `build_compile_context`.
    pub fn declare_intrinsics(&mut self) -> Result<IntrinsicIds, CranelispError> {
        let generic_ids = declare_intrinsics_generic(self.module_mut())?;

        // Store on self for build_compile_context.
        self.alloc_func_id = generic_ids.alloc;
        self.dealloc_func_id = generic_ids.dealloc;
        self.alloc_string_func_id = generic_ids.alloc_string;
        self.panic_func_id = generic_ids.panic;
        self.vec_new_func_id = generic_ids.vec_new;
        self.vec_drop_func_id = generic_ids.vec_drop;

        Ok(IntrinsicIds {
            alloc: generic_ids.alloc.expect("runtime/alloc must be declared"),
            dealloc: generic_ids.dealloc.expect("runtime/dealloc must be declared"),
            alloc_string: generic_ids.alloc_string.expect("runtime/alloc_string must be declared"),
            panic: generic_ids.panic.expect("runtime/panic must be declared"),
            vec_new: generic_ids.vec_new.expect("runtime/vec_new must be declared"),
            vec_drop: generic_ids.vec_drop.expect("runtime/vec_drop must be declared"),
        })
    }

    /// Declare all functions in the JIT module, returning a name->FuncId map.
    /// Used in Batch mode so functions can reference each other.
    pub fn declare_functions(
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
                    span: defn.span,
                })?;
            func_ids.insert(defn.name.clone(), func_id);
        }
        Ok(func_ids)
    }

    /// Declare functions with a module prefix to avoid name collisions in a
    /// shared JIT.
    ///
    /// Each function is declared as `"{prefix}/{name}"` in the JIT. The
    /// returned `func_ids` maps **bare** names to FuncIds (for codegen
    /// within the current module), and `jit_names` maps bare names to
    /// the qualified JIT symbol name (for downstream reference).
    #[allow(clippy::type_complexity)]
    pub fn declare_functions_prefixed(
        &mut self,
        defns: &[&Defn],
        prefix: &str,
    ) -> Result<(HashMap<Symbol, FuncId>, HashMap<Symbol, Symbol>), CranelispError> {
        let mut func_ids = HashMap::new();
        let mut jit_names = HashMap::new();
        for defn in defns {
            let qualified_name = format!("{prefix}/{}", defn.name);
            let sig = self.build_sig(defn.params().len());
            let func_id = self
                .module_mut()
                .declare_function(&qualified_name, Linkage::Export, &sig)
                .map_err(|e| CranelispError::CodegenError {
                    message: format!("failed to declare function '{}': {e}", defn.name),
                    span: defn.span,
                })?;
            func_ids.insert(defn.name.clone(), func_id);
            jit_names.insert(defn.name.clone(), Symbol::from(qualified_name));
        }
        Ok((func_ids, jit_names))
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
    pub fn declare_imported_functions(
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
                    message: format!(
                        "failed to declare imported function '{}': {e}",
                        name
                    ),
                    span: Span::SYNTHETIC,
                })?;
            func_ids.insert(name.clone(), func_id);
        }
        Ok(())
    }

    /// Compile a function definition into Cranelift IR.
    /// Returns the CLIF IR text for introspection.
    ///
    /// The `compile_ctx` bundles all environment needed for codegen: function IDs,
    /// arities, GOT state, and intrinsic IDs. Construct it at the call site using
    /// `Jit::build_compile_context`.
    pub fn compile_defn<C, L>(
        &mut self,
        defn: &Defn,
        compile_ctx: CompileContext<'_, C, L>,
    ) -> Result<CompileArtifacts, CranelispError>
    where
        C: cranelisp_types::CodeStore,
        L: cranelisp_types::LinkerStore,
    {
        self.ctx.func.signature = self.build_sig(defn.params().len());
        self.ctx.func.name =
            cranelift::codegen::ir::UserFuncName::testcase(defn.name.as_bytes());

        // Build the function body.
        // The caller provides the enriched defn (with resolved_call and
        // inferred_type annotations from post-pass enrichment). Do NOT
        // override with the symbol table's ast field — that version has
        // unresolved type variables from the dual-write and lacks post-pass
        // enrichment (resolve_deferred_trait_calls, final substitution).
        // Split-borrow: `compile_body` needs `&mut self.ctx.func`,
        // `&mut self.func_ctx`, and `&mut JITModule` simultaneously. Borrowing
        // the module through a method (`self.module_mut()`) would re-borrow
        // the whole `Jit` — instead reach into the `Option` field directly.
        // Panicking in the `None` arm is unreachable: the module is only
        // `None` inside `Drop::drop`, which cannot coexist with `&mut self`.
        let module = self.module.as_mut().unwrap_or_else(|| {
            unreachable!(
                "invariant: Jit::module is Some for the Jit's entire lifetime"
            )
        });
        FnCompiler::compile_body(
            defn,
            &mut self.ctx.func,
            &mut self.func_ctx,
            module,
            compile_ctx.clone(),
        )?;

        // Capture CLIF IR text before compilation.
        let clif_ir = format!("{}", self.ctx.func.display());

        // Enable disassembly capture.
        self.ctx.set_disasm(true);

        // Compile to machine code.
        let func_id = *compile_ctx
            .func_ids
            .get(&defn.name)
            .ok_or_else(|| CranelispError::CodegenError {
                message: format!("function '{}' not declared", defn.name),
                span: defn.span,
            })?;

        let module = self.module.as_mut().unwrap_or_else(|| {
            unreachable!(
                "invariant: Jit::module is Some for the Jit's entire lifetime"
            )
        });
        module
            .define_function(func_id, &mut self.ctx)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to define function '{}': {e}", defn.name),
                span: defn.span,
            })?;

        // Capture disasm + code size after compilation, before clear_context.
        let (disasm, code_size) = if let Some(compiled) = self.ctx.compiled_code() {
            (
                compiled.vcode.clone(),
                Some(compiled.code_info().total_size as usize),
            )
        } else {
            (None, None)
        };

        let module = self.module.as_mut().unwrap_or_else(|| {
            unreachable!(
                "invariant: Jit::module is Some for the Jit's entire lifetime"
            )
        });
        module.clear_context(&mut self.ctx);

        Ok(CompileArtifacts { clif_ir, disasm, code_size })
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

    /// Build a `CompileContext` from environment parameters.
    ///
    /// Bundles all the information needed for codegen into a single struct,
    /// eliminating the need to pass individual fields to `compile_defn`.
    ///
    /// `symbol_tables` is the shared DashMap of per-module symbol tables.
    /// `current_module` identifies the module being compiled.
    pub fn build_compile_context<'a, C, L>(
        &self,
        func_ids: &'a HashMap<Symbol, FuncId>,
        func_arities: &'a HashMap<Symbol, usize>,
        symbol_tables: &'a dashmap::DashMap<
            cranelisp_types::ModuleFullPath,
            cranelisp_types::SymbolTable<C, L>,
        >,
        current_module: cranelisp_types::ModuleFullPath,
    ) -> CompileContext<'a, C, L>
    where
        C: cranelisp_types::CodeStore,
        L: cranelisp_types::LinkerStore,
    {
        CompileContext {
            func_ids,
            func_arities,
            symbol_tables,
            current_module,
            traced_fns: None,
            alloc_func_id: self.alloc_func_id,
            dealloc_func_id: self.dealloc_func_id.unwrap_or_else(|| {
                unreachable!(
                    "invariant: declare_intrinsics must run before \
                     build_compile_context (Decision 24)"
                )
            }),
            alloc_string_func_id: self.alloc_string_func_id,
            panic_func_id: self.panic_func_id,
            vec_new_func_id: self.vec_new_func_id,
            vec_drop_func_id: self.vec_drop_func_id,
        }
    }

    /// Finalize all pending function definitions.
    pub fn finalize(&mut self) -> Result<(), CranelispError> {
        self.module_mut().finalize_definitions().map_err(|e| {
            CranelispError::CodegenError {
                message: format!("failed to finalize JIT definitions: {e}"),
                span: Span::SYNTHETIC,
            }
        })
    }

    /// Get the finalized code pointer for a function by FuncId.
    pub fn get_finalized_ptr(&self, func_id: FuncId) -> *const u8 {
        self.module().get_finalized_function(func_id)
    }

    /// Finalize definitions and return the code pointer for a named function.
    /// Convenience method that looks up the FuncId by name (re-declaring with
    /// the same param count).
    pub fn finalize_and_get_ptr(
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
                span: Span::SYNTHETIC,
            })?;

        Ok(self.module().get_finalized_function(func_id))
    }

    /// Look up a finalized function pointer by name and param count.
    ///
    /// Must be called after `finalize()`. Re-declares the function with
    /// the same signature to obtain the FuncId, then returns the code pointer.
    pub fn get_ptr_by_name(
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
                span: Span::SYNTHETIC,
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
pub struct IntrinsicIds {
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
#[derive(Default)]
pub struct IntrinsicFuncIds {
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
pub fn declare_intrinsics_generic<M: Module>(
    module: &mut M,
) -> Result<IntrinsicFuncIds, CranelispError> {
    let mut ids = IntrinsicFuncIds::default();

    for sym in intrinsic_symbols() {
        let mut sig = module.make_signature();
        for _ in 0..sym.param_count {
            sig.params.push(AbiParam::new(types::I64));
        }
        if sym.has_return {
            sig.returns.push(AbiParam::new(types::I64));
        }

        let func_id = module
            .declare_function(sym.name, Linkage::Import, &sig)
            .map_err(|e| CranelispError::CodegenError {
                message: format!("failed to declare intrinsic '{}': {e}", sym.name),
                span: Span::SYNTHETIC,
            })?;

        ids.by_name.insert(Symbol::from(sym.name), func_id);

        // Set convenience accessors for the 6 special intrinsics.
        match sym.name {
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
mod tests {
    use super::*;
    use cranelisp_types::DefnVariant;

    // spec: 12-runtime §12.1 — ISA construction for host platform
    #[test]
    fn test_build_isa() {
        let isa = build_isa();
        assert!(isa.is_ok(), "ISA construction should succeed on host");
    }

    // spec: 12-runtime §12.1 — JIT engine creation
    #[test]
    fn test_jit_creation() {
        let jit = Jit::new();
        assert!(jit.is_ok(), "JIT creation should succeed");
    }

    // spec: 12-runtime §12.3 — runtime intrinsic function declarations (alloc, dealloc, panic)
    #[test]
    fn test_intrinsic_declaration() {
        let mut jit = Jit::new().unwrap();
        let ids = jit.declare_intrinsics();
        assert!(ids.is_ok(), "intrinsic declaration should succeed");
    }

    // spec: 08-modules §8.3 — imported function declarations for cross-module calls
    #[test]
    fn test_declare_imported_functions() {
        let mut jit = Jit::new().unwrap();
        let mut func_ids = HashMap::new();

        let imports = vec![
            (Symbol::from("math/add"), 2usize),
            (Symbol::from("math/mul"), 2usize),
        ];
        let result = jit.declare_imported_functions(&imports, &mut func_ids);
        assert!(result.is_ok(), "imported function declaration should succeed");
        assert!(func_ids.contains_key(&Symbol::from("math/add")));
        assert!(func_ids.contains_key(&Symbol::from("math/mul")));
        assert_eq!(func_ids.len(), 2);
    }

    // spec: 08-modules §8.3 — imported declarations merge with local function declarations
    #[test]
    fn test_declare_imported_functions_merges_with_existing() {
        let mut jit = Jit::new().unwrap();

        // Declare a local function first.
        let defn = Defn {
            name: Symbol::from("local_fn"),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![Symbol::from("x")],
                param_annotations: vec![],
                body: cranelisp_types::Expr::Var {
                    name: Symbol::from("x"),
                    span: Span::new(0, 1),
                    inferred_type: None,
                },
                span: Span::new(0, 10),
            }],
            visibility: cranelisp_types::Visibility::Public,
            span: Span::new(0, 10),
        };
        let mut func_ids = jit.declare_functions(&[&defn]).unwrap();
        assert_eq!(func_ids.len(), 1);

        // Now declare an imported function -- should merge into the same map.
        let imports = vec![(Symbol::from("other/helper"), 1usize)];
        jit.declare_imported_functions(&imports, &mut func_ids).unwrap();
        assert_eq!(func_ids.len(), 2);
        assert!(func_ids.contains_key(&Symbol::from("local_fn")));
        assert!(func_ids.contains_key(&Symbol::from("other/helper")));
    }

    // spec: pipeline-orchestration §4 — JIT with extra symbols for cross-module calls
    #[test]
    fn test_jit_new_with_symbols() {
        // An empty extra_symbols list should work identically to new().
        let jit = Jit::new_with_symbols(&[]);
        assert!(jit.is_ok(), "new_with_symbols with empty list should succeed");

        // Extra symbols should be accepted (though we can't call them in
        // this unit test, we verify the builder doesn't reject them).
        extern "C" fn dummy_fn(_x: i64) -> i64 {
            0
        }
        let jit2 = Jit::new_with_symbols(&[("test/dummy", dummy_fn as *const u8)]);
        assert!(
            jit2.is_ok(),
            "new_with_symbols with extra symbol should succeed"
        );
    }

    // spec: design/arch/CLAUDE.md Decision 31 — custom `Drop` on `Jit` calls
    // `unsafe JITModule::free_memory()` to reclaim mmap'd executable pages.
    // Without this, Cranelift's default `Memory::drop` leaks
    // (cranelift-jit-0.116.1/src/memory.rs:269-276 — `mem::forget`s every
    // allocation).
    #[test]
    fn drop_runs_without_panic() {
        // A freshly-constructed JIT with no compiled code must still drop
        // cleanly — free_memory must tolerate a JIT that has never had
        // anything finalised.
        let jit = Jit::new().expect("JIT construction");
        drop(jit);
        // Reaching here means the drop path returned without panic.
    }

    // spec: design/arch/CLAUDE.md Decision 31 — reclaim path executes on drop.
    #[test]
    fn drop_invokes_free_memory() {
        use std::sync::atomic::Ordering;

        let before = JIT_FREE_MEMORY_CALL_COUNT.load(Ordering::Relaxed);
        {
            let _jit = Jit::new().expect("JIT construction");
            // Declaring intrinsics exercises the JIT's declare path so this
            // isn't a trivial empty-module case. `_jit` drops at end of
            // scope.
            let mut jit = _jit;
            jit.declare_intrinsics().expect("intrinsics declare");
            drop(jit);
        }
        let after = JIT_FREE_MEMORY_CALL_COUNT.load(Ordering::Relaxed);
        assert_eq!(
            after, before + 1,
            "Jit::drop must call free_memory exactly once (counter before={before}, after={after})"
        );
    }

    // spec: design/arch/CLAUDE.md Decision 31 — normal compile+call+drop
    // flow continues to work after the reclaim machinery is in place. This
    // checks that the `Option<JITModule>` plumbing does not regress the
    // finalize/get-ptr/call path. We observe the correct return value
    // **before** drop (post-drop derefs are UB); the drop itself then fires
    // and must not panic.
    #[test]
    fn compile_call_drop_roundtrip() {
        use cranelisp_types::{Expr, Type, Visibility};
        use std::sync::atomic::Ordering;

        let mut jit = Jit::new().expect("JIT construction");
        jit.declare_intrinsics().expect("intrinsics declare");

        // Zero-arg fn returning the literal 42.
        let name = Symbol::from("trivial_fortytwo");
        let defn = Defn {
            name: name.clone(),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                param_annotations: vec![],
                body: Expr::IntLit {
                    value: 42,
                    span: Span::SYNTHETIC,
                    inferred_type: Some(Box::new(Type::Int)),
                },
                span: Span::SYNTHETIC,
            }],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        };

        let func_ids = jit.declare_functions(&[&defn]).expect("declare");
        let func_arities: HashMap<Symbol, usize> = HashMap::new();
        let symbol_tables: dashmap::DashMap<
            cranelisp_types::ModuleFullPath,
            cranelisp_types::SymbolTable,
        > = dashmap::DashMap::new();
        let module_path = cranelisp_types::ModuleFullPath::from("user");
        symbol_tables.insert(
            module_path.clone(),
            cranelisp_types::SymbolTable::new(module_path.clone()),
        );

        let compile_ctx = jit.build_compile_context(
            &func_ids,
            &func_arities,
            &symbol_tables,
            module_path,
        );
        jit.compile_defn(&defn, compile_ctx).expect("compile");
        let ptr = jit.finalize_and_get_ptr(&name, 0).expect("finalize");
        assert!(!ptr.is_null(), "finalized pointer must be non-null");

        // SAFETY: the JIT is still alive (we hold the only handle to it);
        // the function was just finalized with signature `extern "C" fn() -> i64`.
        let f: extern "C" fn() -> i64 = unsafe { std::mem::transmute(ptr) };
        let result = f();
        assert_eq!(result, 42, "trivial fn must return 42 before drop");

        // Now drop and confirm the reclaim counter incremented.
        let before = JIT_FREE_MEMORY_CALL_COUNT.load(Ordering::Relaxed);
        drop(jit);
        let after = JIT_FREE_MEMORY_CALL_COUNT.load(Ordering::Relaxed);
        assert_eq!(
            after, before + 1,
            "Drop after compile+call must still invoke free_memory"
        );
    }

    // spec: design/arch/CLAUDE.md Decision 23 (Sprint 58 Wave 2 follow-on) —
    // unified GOT data symbol shape: the symbol address IS the per-module
    // slab base directly, with NO extra pointer-cell indirection. In JIT
    // mode this is achieved by registering `__cranelisp_got_{M}` via
    // `JITBuilder::symbol()` (passed through `extra_symbols`) so the
    // lookup-fn returns the slab base; CLIF emitted by
    // `emit_got_indirect_call_via_data_id` then does one `global_value`
    // (= ADRP+LDR through the system GOT) + one slot offset + one slot
    // load. This test compiles a function that takes the symbol's address
    // via `global_value` and asserts the address equals the registered
    // slab base — i.e. the registered address is NOT a separate pointer
    // cell that itself contains the slab base.
    #[test]
    fn jit_got_symbol_address_is_slab_base() {
        use cranelisp_types::{Defn, DefnVariant, Expr, Type, Visibility};
        use cranelift_module::Linkage;
        use std::sync::atomic::{AtomicU64, Ordering};

        // Use a static, address-stable backing storage as the "slab base".
        // The test asserts that `__cranelisp_got_test_module` resolves to
        // exactly this address (no extra deref).
        static SLAB: AtomicU64 = AtomicU64::new(0xDEAD_BEEF_CAFE_F00D);
        let slab_base_ptr: *const u8 = &SLAB as *const _ as *const u8;

        let got_sym = "__cranelisp_got_test_module";
        let mut jit = Jit::new_with_symbols(&[(got_sym, slab_base_ptr)])
            .expect("JIT construction with GOT symbol");
        jit.declare_intrinsics().expect("intrinsics");

        // Compile a fn that returns the *address* of the GOT data symbol —
        // this is what `global_value` resolves to inside the unified GOT
        // call sequence. If JIT registration is correct, the returned i64
        // equals `slab_base_ptr as u64` (no extra pointer-cell deref).
        let name = Symbol::from("get_got_addr");
        let body = Expr::IntLit {
            value: 0,
            span: Span::SYNTHETIC,
            inferred_type: Some(Box::new(Type::Int)),
        };
        let defn = Defn {
            name: name.clone(),
            docstring: None,
            variants: vec![DefnVariant {
                params: vec![],
                param_annotations: vec![],
                body,
                span: Span::SYNTHETIC,
            }],
            visibility: Visibility::Public,
            span: Span::SYNTHETIC,
        };

        // Declare the function and build a context, then hand-write the body
        // so the test does not depend on the broader codegen pipeline. The
        // body is: declare `__cranelisp_got_test_module` as Import data,
        // take its address via `global_value`, return it as i64.
        let func_ids = jit.declare_functions(&[&defn]).expect("declare");
        let func_id = *func_ids.get(&name).expect("func_id");

        // Build the body by reaching into the JIT module directly.
        {
            let module = jit.jit_module();
            let mut sig = module.make_signature();
            sig.returns.push(cranelift::prelude::AbiParam::new(
                cranelift::prelude::types::I64,
            ));
            let mut ctx = module.make_context();
            ctx.func.signature = sig;
            ctx.func.name = cranelift::codegen::ir::UserFuncName::testcase(name.as_bytes());

            let data_id = module
                .declare_data(got_sym, Linkage::Import, false, false)
                .expect("declare GOT data");

            let mut fbc = FunctionBuilderContext::new();
            {
                let gv = module.declare_data_in_func(data_id, &mut ctx.func);
                let mut fb = cranelift::prelude::FunctionBuilder::new(&mut ctx.func, &mut fbc);
                let entry = fb.create_block();
                fb.switch_to_block(entry);
                fb.seal_block(entry);
                let addr = fb
                    .ins()
                    .global_value(cranelift::prelude::types::I64, gv);
                fb.ins().return_(&[addr]);
                fb.finalize();
            }
            module
                .define_function(func_id, &mut ctx)
                .expect("define_function");
            module.clear_context(&mut ctx);
        }

        let ptr = jit.finalize_and_get_ptr(&name, 0).expect("finalize");
        // SAFETY: the JIT is still alive; signature is `extern "C" fn() -> i64`.
        let f: extern "C" fn() -> i64 = unsafe { std::mem::transmute(ptr) };
        let returned = f() as u64;

        assert_eq!(
            returned,
            slab_base_ptr as u64,
            "JIT-resolved address of __cranelisp_got_test_module must equal \
             the registered slab base directly (no pointer-cell indirection); \
             returned={:#x}, expected={:#x}",
            returned,
            slab_base_ptr as u64,
        );

        // Regression guard: read the SLAB content. If the JIT had defined
        // the symbol as a pointer cell containing the slab base, the
        // returned address would point INTO `SLAB` (and `*returned == SLAB`).
        // With the correct registration, the returned address IS
        // `&SLAB`, so `*returned == SLAB.load()`. The two are
        // distinguishable only when the registered symbol address is the
        // slab itself: confirm by reading 8 bytes at the returned address.
        let read = unsafe { std::ptr::read_unaligned(returned as *const u64) };
        assert_eq!(
            read,
            SLAB.load(Ordering::Relaxed),
            "Address returned must point AT the slab (so dereferencing it \
             yields the slab's first word), confirming no intermediate \
             pointer cell exists."
        );
    }

    // spec: design/arch/CLAUDE.md Decision 23 — cross-module dispatch via
    // GOT-indirect call. Two synthetic modules: producer module owns a fn
    // returning 99 with its pointer placed at slot 7 of a heap-allocated
    // slab; consumer module compiles a thunk that loads slot 7 from the
    // producer's GOT and tail-calls through it. Asserts the round-trip
    // returns 99, exercising the full unified call shape end-to-end.
    #[test]
    fn jit_cross_module_got_dispatch_end_to_end() {
        use cranelift_module::Linkage;
        use std::alloc::{alloc_zeroed, Layout};

        // 1. Build a "producer" JIT, compile `producer_fn` returning 99.
        //    Read out its finalised pointer.
        let producer_ptr: *const u8 = {
            use cranelisp_types::{Defn, DefnVariant, Expr, Type, Visibility};
            let mut jit = Jit::new().expect("producer JIT");
            jit.declare_intrinsics().expect("intrinsics");
            let name = Symbol::from("producer_fn");
            let defn = Defn {
                name: name.clone(),
                docstring: None,
                variants: vec![DefnVariant {
                    params: vec![],
                    param_annotations: vec![],
                    body: Expr::IntLit {
                        value: 99,
                        span: Span::SYNTHETIC,
                        inferred_type: Some(Box::new(Type::Int)),
                    },
                    span: Span::SYNTHETIC,
                }],
                visibility: Visibility::Public,
                span: Span::SYNTHETIC,
            };
            let func_ids = jit.declare_functions(&[&defn]).expect("declare");
            let func_arities: HashMap<Symbol, usize> = HashMap::new();
            let symbol_tables: dashmap::DashMap<
                cranelisp_types::ModuleFullPath,
                cranelisp_types::SymbolTable,
            > = dashmap::DashMap::new();
            let module_path = cranelisp_types::ModuleFullPath::from("producer");
            symbol_tables.insert(
                module_path.clone(),
                cranelisp_types::SymbolTable::new(module_path.clone()),
            );
            let compile_ctx =
                jit.build_compile_context(&func_ids, &func_arities, &symbol_tables, module_path);
            jit.compile_defn(&defn, compile_ctx).expect("compile");
            let ptr = jit.finalize_and_get_ptr(&name, 0).expect("finalize");
            // Leak `jit` so the code pages stay live for the duration of the test.
            std::mem::forget(jit);
            ptr
        };

        // 2. Allocate a 16-slot slab on the heap, write `producer_ptr` at slot 7.
        let slot = 7usize;
        let slab_size = 16 * 8;
        let layout = Layout::from_size_align(slab_size, 8).unwrap();
        let slab_base: *mut u8 = unsafe { alloc_zeroed(layout) };
        unsafe {
            let slot_addr = slab_base.add(slot * 8) as *mut u64;
            slot_addr.write(producer_ptr as u64);
        }

        // 3. Build a consumer JIT with `__cranelisp_got_producer` registered
        //    pointing at the slab base directly (Decision 23 — symbol
        //    address IS the slab base, no pointer-cell indirection).
        let got_sym = "__cranelisp_got_producer";
        let mut consumer = Jit::new_with_symbols(&[(got_sym, slab_base as *const u8)])
            .expect("consumer JIT");
        consumer.declare_intrinsics().expect("intrinsics");

        // 4. Hand-build a thunk that emits the unified GOT call shape:
        //    slab = global_value(__cranelisp_got_producer)
        //    fn_ptr = load(slab + slot * 8)
        //    return call_indirect(fn_ptr)
        let thunk_name = Symbol::from("consumer_thunk");
        let thunk_id = {
            let module = consumer.jit_module();
            let mut sig = module.make_signature();
            sig.returns.push(cranelift::prelude::AbiParam::new(
                cranelift::prelude::types::I64,
            ));
            let id = module
                .declare_function(&thunk_name, Linkage::Export, &sig)
                .expect("declare thunk");
            let data_id = module
                .declare_data(got_sym, Linkage::Import, false, false)
                .expect("declare GOT data");

            let mut ctx = module.make_context();
            ctx.func.signature = sig.clone();
            ctx.func.name =
                cranelift::codegen::ir::UserFuncName::testcase(thunk_name.as_bytes());
            let mut fbc = FunctionBuilderContext::new();
            {
                let gv = module.declare_data_in_func(data_id, &mut ctx.func);
                let mut fb = cranelift::prelude::FunctionBuilder::new(&mut ctx.func, &mut fbc);
                let entry = fb.create_block();
                fb.switch_to_block(entry);
                fb.seal_block(entry);
                let slab = fb
                    .ins()
                    .global_value(cranelift::prelude::types::I64, gv);
                let slot_addr = fb.ins().iadd_imm(slab, (slot * 8) as i64);
                let fn_ptr = fb.ins().load(
                    cranelift::prelude::types::I64,
                    cranelift::prelude::MemFlags::trusted(),
                    slot_addr,
                    0,
                );
                let mut callee_sig = module.make_signature();
                callee_sig.returns.push(cranelift::prelude::AbiParam::new(
                    cranelift::prelude::types::I64,
                ));
                let sig_ref = fb.import_signature(callee_sig);
                let call = fb.ins().call_indirect(sig_ref, fn_ptr, &[]);
                let result = fb.inst_results(call)[0];
                fb.ins().return_(&[result]);
                fb.finalize();
            }
            module
                .define_function(id, &mut ctx)
                .expect("define thunk");
            module.clear_context(&mut ctx);
            id
        };

        consumer.finalize().expect("finalize consumer");
        let thunk_ptr = consumer.get_finalized_ptr(thunk_id);
        // SAFETY: thunk just finalised; signature is `extern "C" fn() -> i64`.
        let thunk: extern "C" fn() -> i64 = unsafe { std::mem::transmute(thunk_ptr) };
        let result = thunk();
        assert_eq!(
            result, 99,
            "Cross-module GOT dispatch must round-trip the producer's return value (99)"
        );

        // Cleanup: drop consumer JIT (producer was forgotten — the slab
        // and its slot pointer remain valid for the duration of `result`'s
        // computation, and we deliberately leak both for test simplicity).
        drop(consumer);
        // SAFETY: nothing reads `slab_base` after this point.
        unsafe { std::alloc::dealloc(slab_base, layout) };
    }
}
