# Facade spec — `crates/cranelisp-backend/`

**Bounded context citation.** Typed AST → Cranelift IR → executable. Owns codegen, RC, JIT lifecycle, caching, and linking. Paired with runtime. See `bounded-contexts.md` §3 — Backend.

This spec is **target-stating**. Drift detection between as-designed and as-built is the job of `cargo-public-api` (M4-pending) and `/review`'s per-PR audit, not this document.

---

## Public surface (as-designed)

### Free functions — the three codegen entry points

These are the entire backend boundary used by `int`'s priority workers (JIT path) and nice workers (object path).

```rust
pub fn compile_to_module<M: Module>(
    scope: &ModuleFullPath,
    names: &[Symbol],
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable<Code, ()>>,
    introspection: Option<&DashMap<FQSymbol, Introspection>>,
    module: M,
) -> Result<(), CompilationError>;

pub fn load_object(
    module: &ModuleFullPath,
    object: &[u8],
    symbol_tables: &SymbolTables,
) -> Result<LinkerArtefact, CranelispError>;

pub fn compile_to_object(
    module: &ModuleFullPath,
    symbol_tables: &SymbolTables,
) -> Result<ObjectArtefact, CranelispError>;
```

`compile_to_module` is the codegen entry — used by `int`'s priority workers (JIT path) and nice workers (object path). Generic over `M: cranelift_module::Module` per Decision 23 — the same body emits byte-identical CLIF whether `M` is a `JITModule` or an `ObjectModule`; the mode is a property of which `Module` instance the caller passes. **Cardinality is determined by the `names` arity at the caller, NOT by mode** — JIT mode passes one symbol per call (per Decision 41 — true per-symbol JIT for per-redefinition reclaim); object mode passes the full module's defined symbols (per-module ObjectModule).

Per Decision 41 (S66 amendment + rollback `1dc57ae`), backend writes each compiled symbol's lifecycle owner via Decision 38's `write_code(&self, sym, code)` with `code = Code::Jit(Arc<Jit>)` (interior mutable; no `&mut` flow needed) AND writes the resulting fn pointer to the entry's GOT slot via `symbol_table.got().store_slot(entry.got_slot.unwrap(), ptr)` — the GOT is the post-rollback single source of truth for callable addresses (no per-entry sibling `fn_ptr` field). Backend also writes `Introspection { clif_ir, disasm, code_size, compile_duration }` into the introspection map iff `introspection.is_some()` — the `Option`'s `is_some()` IS Decision 38's mode discriminator, reaching backend directly via the parameter. There is no return tuple to unpack; `int`'s previous post-loop (worker.rs:2860-3018) collapses into the per-symbol call-site loop. Decision 37's "no swallowed failures" rule lands as a single `?` inside `compile_to_module` — the per-step cascade collapses; backend errors out at the first invariant breach with a typed `CompilationError` variant.

`load_object` is the JIT-mode cache-hit entry — reads a `.o` produced by an earlier `compile_to_object` call (or by `--link` mode), runs the cache `Linker` to resolve each defined symbol's address, returns a `LinkerArtefact` that `int` consumes to populate per-symbol `code = Code::Linker(Arc<Linker>)` (lifecycle owner) and writes the per-symbol address to the entry's GOT slot via `got().store_slot(entry.got_slot.unwrap(), ptr)` on each `ST[m].symbols[name]` entry. Per-module cardinality (one Linker holds many symbols) is unchanged; the per-symbol direct-write pattern is for `compile_to_module` only.

`compile_to_object` is the nice-worker object-codegen entry — produces the `.o` artefact + sidecar (`.meta.json` containing the serialised `SymbolTable<(), ()>`). Backend writes nothing to disk itself; `int`'s `ObjectCache::write` does the file IO.

### Return shapes

`compile_to_module` returns `Result<(), CompilationError>` — no artefact struct. Backend writes Code and Introspection directly into the passed-in stores per Decision 41.

```rust
#[non_exhaustive]
pub struct LinkerArtefact {
    pub linker: Arc<Linker>,                                   // per-module retention root for cache-hit code — analogous to Jit for JIT mode
    pub ptrs: HashMap<Symbol, *const u8>,                      // per-symbol code addresses; `int` writes each to `symbol_table.got().store_slot(entry.got_slot.unwrap(), ptr)` (the post-rollback single source of truth) and stores `Code::Linker(linker.clone())` as the lifecycle owner
}

#[non_exhaustive]
pub struct ObjectArtefact {
    pub object: Vec<u8>,                                       // ELF or Mach-O bytes — host-platform native
    pub sidecar: SymbolTable<(), ()>,                          // serialised SymbolTable for the cache .meta.json (no code, no linker)
}
```

### `Code` — the per-symbol lifecycle owner (moved here from `src/` per Decision 41; slimmed per S66 — variant slim preserved through the same-day fn_ptr-unification rollback)

```rust
#[non_exhaustive]
pub enum Code {
    Jit(Arc<Jit>),                                             // fresh-build code; Arc<Jit> is the Decision-31 reclaim primitive
    Linker(Arc<Linker>),                                       // cache-hit code mapped from .o via load_object
}

unsafe impl Send for Code {}
unsafe impl Sync for Code {}
```

**`Code` carries lifecycle ownership ONLY.** The fn ptr for an indirect call lives in the per-module `GotTable` — read via `symbol_table.got().load_slot(entry.got_slot.unwrap())`. The S66 unification (`b09ec76`) briefly relocated the per-entry ptr to a sibling `ModuleEntry::Def.fn_ptr` field; the same-day rollback `1dc57ae` removed that field as redundant with the GOT (which was already authoritative — every callable entry already had a `got_slot`, and JIT-emitted code reads addresses from `got_base + slot * 8`). Post-rollback the GOT is the single source of truth for callable addresses — multi-origin: JIT user fn, linker-loaded user fn, primitive, platform DLL fn (see `facades/types.md` §"Symbol table — the single store"). Variants here distinguish JIT-side reclaim semantics (Decision 31 Scenario 2 — `Arc<Jit>::Drop` calls `JITModule::free_memory()` once refcount hits 0) from linker-loaded persistence (cache-hit reload — `Arc<Linker>` holds the mmap'd object alive). Primitives and platform DLL fns set `code = None` because their lifecycle owners live elsewhere (process-static `LazyLock<SymbolTable>` for primitives; `SharedState.kept_dlls` for platform).

To extract the fn ptr from a callable entry, **read the GOT slot**: `symbol_table.got().load_slot(entry.got_slot.unwrap())`. Do NOT match on `Code` variants for ptr access. The variant-uniform `Code::ptr()` accessor that previously lived here is removed — there is no ptr inside `Code` to accessor over.

`Code` is the integration layer's concrete `C` for `SymbolTable<C, L>`, but its definition lives in `cranelisp-backend` because both variants reference backend-owned types (`Jit`, `Linker`). Decision 35's Principle-3 protection (no `cranelisp-types → cranelisp-backend` dep) survives intact — `Code` does NOT live in `cranelisp-types`. Decision 35 Layer 2 Option B retracts: backend now constructs `Code` directly (per Decision 41), so the integration layer is no longer the sole crate that names `Code`.

**Decision 31 Scenario 2 preserved.** Lifecycle ownership stays inside `Code::Jit(Arc<Jit>)`. When a user redefines a fn, the old `ModuleEntry::Def` drops, its `Code::Jit(Arc<Jit>)` drops, refcount → 0 if last reference, custom `Drop` on `Jit` fires, `JITModule::free_memory()` runs. The GOT slot's stored ptr becomes invalid the instant the JIT pages are freed — same lifecycle semantics as either of the considered field placements (in-variant ptr or sibling `fn_ptr`); the address now has its single home in the GOT.

### Errors

```rust
#[non_exhaustive]
pub enum CompilationError {
    /// Per Decision 37 + §2.7 — a name passed in `names` does not resolve to a
    /// compilable entry in the symbol table. Indicates either a stale caller
    /// (the entry was evicted between `defined_symbols()` and the call) or a
    /// contract violation (caller passed a name that was never compilable —
    /// e.g., `kind == Overloaded` or `ast: None`).
    SymbolNotCompilable { module: ModuleFullPath, symbol: Symbol },

    /// Cranelift codegen failed for a defined symbol.
    CodegenFailed { module: ModuleFullPath, symbol: Symbol, cause: String, location: ErrorLocation },

    /// `JITModule::define_function` or `Module::declare_function` returned an error.
    ModuleError { module: ModuleFullPath, symbol: Symbol, cause: String },

    /* … */
}
```

Per §2.7 — `SymbolNotCompilable` is the typed signal for the Decision-37 failure mode. Replaces ad-hoc `CranelispError::CodegenError { message: "..." }` strings at the boundary; callers can match on the variant rather than parse messages.

```rust
#[non_exhaustive]
pub enum LinkerError {
    /// Symbol not found in the loaded object's resolved symbol set.
    /// Pre-S58 silent-NULL regression net per Decision 37 — this variant
    /// is what the integration layer matches on at cache-hit failure.
    SymbolNotFound { name: LinkerSymbol },

    /// Object relocation pass produced an error during `load_object` or
    /// per-symbol resolution. Signals corruption, ABI mismatch, or
    /// unresolved external reference.
    RelocationFailed { name: LinkerSymbol, cause: String },
}
```

`LinkerError` is the typed result of `Linker::get_symbol` (Decision 36 — bare-name lookup) and other per-symbol cache-load operations. Per Decision 37, asking for a symbol that isn't there is a typed error, not a bare `Option`. The two-variant baseline is the minimum surface acceptable at S66 close — additional variants (e.g., `MmapFailed`, `MachOParseError`, `AbiMismatch`) extend as evidence accrues from production traces; the `#[non_exhaustive]` attribute admits future additions without a public-API break. Re-shape may be triggered during /review of a future FIXME if the variant set proves insufficient.

### `Jit` — the JIT retention newtype (Decision 31)

```rust
pub struct Jit {
    inner: cranelift_jit::JITModule,
}

impl Jit {
    pub fn new(builder: JITBuilder) -> Self;
    pub fn module(&mut self) -> &mut JITModule;
}

impl Drop for Jit {
    fn drop(&mut self) {
        // Decision 31 — Cranelift 0.116's default Memory::drop leaks on purpose.
        // Custom Drop calls unsafe { self.inner.free_memory() } to reclaim executable pages.
        // SAFETY: Arc<Jit> refcount reaching 0 means no derived fn pointer is reachable —
        // see Decision 31 evidence + safety invariant.
    }
}

unsafe impl Send for Jit {}
unsafe impl Sync for Jit {}
```

Wrapped in `Arc<Jit>` by `compile_to_module`; the Arc lives on `ModuleEntry::Def.code = Code::Jit(Arc<Jit>)` per Decision 35 (S66 amendment + rollback — variant carries lifecycle owner only; the fn ptr lives in `SymbolTable.got()` indexed by `ModuleEntry::Def.got_slot`). When the last clone drops (REPL redefinition or session shutdown), executable memory is reclaimed.

### `Linker` — the cache-load retention newtype

```rust
pub struct Linker {
    /* internal — wraps a memory-mapped object file + relocation state */
}

impl Linker {
    pub fn load_object(object: &[u8]) -> Result<Self, CranelispError>;
    pub fn get_symbol(&self, name: &LinkerSymbol) -> Result<*const u8, LinkerError>;  // Decision 36 — bare-name lookup (Linkage::Local); §2.6 — typed result, dedicated newtype
}

unsafe impl Send for Linker {}
unsafe impl Sync for Linker {}
```

Wrapped in `Arc<Linker>` by `load_object`; analogous lifecycle to `Jit`. `Arc<Linker>` lives on `ModuleEntry::Def.code = Code::Linker(Arc<Linker>)` for cache-hit modules (S66 amendment + rollback — the per-symbol fn ptr lives in `SymbolTable.got()` indexed by `ModuleEntry::Def.got_slot`).

### Cache submodule

The `cache::` submodule (linker + manifest + object + serialize) carries ~60 pub items. The per-item disposition + per-submodule public surface enumeration lives in **`facades/backend-cache.md`** — the dedicated sub-facade. Items above (`Linker`, `LinkerArtefact`, `LinkerError`) are the boundary items the parent facade names; sub-facade enumerates the full cache public surface plus the doubled root-level re-export layer (Wave 4 narrowing target).

### GOT-population observation (extension point)

NOT diagnostics — an extension point in the same shape as intrinsics' `IoObserver` (Decision 40 + Decision 43 — the IoObserver registration API resides in `cranelisp-intrinsics` post-D43; see `facades/intrinsics.md` §"IO observation"). Backend defines the observation taxonomy and a registration API; `int` implements all observer state. The events fire from `compile_to_module`'s `write_code` site (where the data is in hand) and from `Linker::load_object`'s slot population. Production batch (no observer registered) pays one relaxed null-check load per call site.

```rust
pub enum GotEventTag { JitWrite, LinkerWrite, Redefinition, /* … */ }
pub struct GotEvent {
    pub module: ModuleFullPath,
    pub symbol: Symbol,
    pub slot: usize,
    pub ptr: *const u8,
    pub provenance: GotProvenance,           // Jit { jit_addr: usize } | Linker { linker_addr: usize }
}
pub type GotObserver = fn(GotEventTag, &GotEvent);

/// Replaces the current observer atomically. Thread-safe from any thread;
/// last write wins under happens-before ordering. Pass `None` to unregister.
/// Subsequent GOT-population events emitted from `compile_to_module`'s
/// `write_code` site and from `Linker::load_object` slot population are
/// delivered to the observer most recently registered (in happens-before
/// order). Callers do not reason about Acquire/Release — the API commits
/// to the contract.
pub fn register_got_observer(observer: Option<GotObserver>);
```

`GotEventTag` and `GotEvent` move with the API to backend — they ARE the callback's type contract; they belong where the GOT writes happen. `int`'s startup (REPL/trace mode OR `CRANELISP_GOT_TRACE=1`) calls `cranelisp_backend::register_got_observer(Some(int::got_trace::record))`. The observer state (per-thread `VecDeque` ring buffer, FIFO overflow, formatter, dump) lives in `src/got_trace/` parallel to `src/io_trace/` post-Decision-40 relocation. This is the third instance of the project's consistent observability pattern (alongside `io_trace` and `scheduler_trace`).

### Public consts

None.

---

## Internal-but-exposed surface

The items below are `pub` in `cranelisp-backend` today but are NOT part of the as-designed boundary contract. They exist as `pub` for one of two reasons: (a) test-side instantiation by integration-tier or unit-tier tests in the workspace (the three-tier helpers reference internal codegen state); (b) cross-submodule consumers within backend itself that haven't yet been narrowed to `pub(crate)`. Each item is named here so `tests/facade_compliance.rs` recognises it as a known internal exposure; Wave 3+ `/dev (backend)` is the agent that may choose to narrow further to `pub(crate)` once consumers are mapped.

Per the Sprint 67 brief: items in this section are PFR (pull facade to reality — internal surface that exists by design, not by oversight) rather than PIF (push implementation to facade — surface that should disappear). The two PIF residues remaining at the time of this facade are explicit and named in §"Non-goals" + the Wave 3 PIF list below.

### Codegen-orchestration internals (Row 10)

These are the per-function compilation primitives. `int`'s priority/nice workers reach for them only via the free function `compile_to_module`; test code in `crates/cranelisp-backend/src/*/tests` and in `tests/legacy/` directly constructs them. They are `pub` so those tests compile.

- `compiler::FnCompiler<'a, M, C, L>` — the per-function CLIF emitter; owns a `FunctionBuilder` + `&mut M: Module`. `compile_body` and `compile_expr` are its two methods. Construction goes via `compile_body` (static entry); `compile_expr` is the recursive workhorse, public for test-side AST-fragment compilation.
- `compiler::CompileContext<'a, C, L>` — the bundle of shared state threaded into every `FnCompiler`: intrinsic `FuncId`s (`alloc_func_id`, `alloc_string_func_id`, `dealloc_func_id`, `panic_func_id`, `vec_drop_func_id`, `vec_new_func_id`), the symbol-table reference, the current module path, per-call `func_arities` + `func_ids` resolution tables, and optional `traced_fns`. The two helper methods `lookup_constructor` and `lookup_type_def` probe the symbol table for ADT metadata at codegen time.
- `compiler::MatchContext` — per-arm state for `compile_match` (the scrutinee value `scrut_val`, optional `scrut_type`, the saved-tail flag `saved_tail`, the `merge_block` for arm-result phi, the `next_block` for fallthrough). Public for unit tests of match-arm codegen.
- `compiler::TracedFnInfo` — per-fn trace metadata (name, arity, code_ptr, got_base, got_slot, param_types, result_type). Populated by `int`'s trace mode and threaded through `CompileContext::traced_fns`. The fields are public because trace observer code in `int` constructs the records directly.
- `compiler::MATCH_EXHAUSTION_TRAP: u8` — the trap code emitted at match-exhaustion sites; named in CLIF and matched by `cranelisp_panic`-side decoders.

### Compiler submodules (Row 10 expanded)

The internal organisation of `compiler` exposes five public submodules: `apply`, `control_flow`, `literals`, `match_codegen`, `trace_codegen`, `vec_codegen`. Each holds the codegen for one syntactic category. They are `pub` because per-submodule unit tests live alongside (`#[cfg(test)] mod tests` inside each), and because cross-submodule helper functions occasionally call across (`compile_apply` reaches into `compile_match` for tail-position arms). Narrowing to `pub(crate)` is a Wave 3+ cleanup that does not affect the boundary contract; `tests/facade_compliance.rs` recognises the submodule names as covered here.

### GOT-target resolution helpers (Row 11)

- `compiler::resolve_func_arity` — given `(symbol_tables, current_module, name)`, returns the callee's arity. Used at every call-site to validate the call's argument count matches the callee's declared parameter count.
- `compiler::resolve_got_target` — given `(symbol_tables, current_module, name)`, returns `(target_module, got_slot)` — the per-module GOT location for the callee. The core indirect-call resolution per Decision 23's two-GOT model.
- `compiler::got_data_symbol_name` — duplicate name in scope of `cache::object::got_data_symbol_name` (Row 11 — the two are the same function; the cache home is canonical; the `compiler::` re-export is a convenience for the call-site that emits the relocation). Narrows to `pub(crate)` in Wave 3+ when call-site routing through `cache::object::got_data_symbol_name` is mechanical.
- `compiler::MATCH_EXHAUSTION_TRAP` — already named above.

Disposition: PFR for `resolve_func_arity` + `resolve_got_target` (they are the canonical resolution primitives — no equivalent at the `cranelisp-types` boundary because per-symbol-table probing is backend-internal); PIF candidate for `compiler::got_data_symbol_name` (duplicate naming with `cache::object::got_data_symbol_name`). Wave 3+ `/dev (backend)` may file a FIXME to narrow the `compiler::` form.

### Module / submodule re-exports (Row 7 / Row 14 confirmation)

- `codegen_types` — re-exports `GOT_TABLE_SIZE` + `NULLARY_TAG_THRESHOLD` from `cranelisp-types`. The submodule exists for module-level grouping of size constants that codegen sites reach for during CLIF emission. Per Principle 15 — these consts originate in `cranelisp-types`; the re-export at `cranelisp_backend::codegen_types` is a convenience-only path. Narrows to `pub(crate)` candidate.
- `got` — exposes `GotTable` (re-export from `cranelisp-types`). Backend constructs `GotTable` at GOT initialisation; the re-export gives callers `cranelisp_backend::got::GotTable` as a convenience path. Principle 15 — `GotTable` originates in `cranelisp-types`; the re-export is `pub(crate)`-narrowable. The `got` submodule itself is `pub` so the re-exported `GotTable` name surfaces.
- `got_observer` — already a top-level §"GOT-population observation" surface. The submodule path exposes the same names. The free function `emit` (the observer-side dispatch entry) is internal-but-exposed for backend codegen sites that invoke it; tests reach into it directly. `register_got_observer` is the canonical registration entry per Row 14.
- `heap` — exposes RC primitives, ADT heap layout structs, last-use analysis, and emit helpers. The heap layout structs `HeapAdt`, `HeapClosure`, `HeapVec` (with `#[repr(C)]` fields `header`, `tag`, `cap`, `data_ptr`, `len`, `code_ptr`, `drop_glue_ptr` + offset consts `TAG_OFFSET`, `FIELDS_START`, `CAPTURES_START`, `CODE_PTR_OFFSET`, `DROP_GLUE_PTR_OFFSET`, `CAP_OFFSET`, `DATA_PTR_OFFSET`, `LEN_OFFSET`, and the helper consts/functions `field_offset`, `payload_size`, `capture_offset`, `NULLARY_THRESHOLD_I64`) are the runtime layout contract that intrinsics and codegen agree on. They are `pub` because `cranelisp-intrinsics` reads layouts and codegen emits offset-keyed loads using the same constants. Emit helpers `emit_alloc`, `emit_rc_inc`, `emit_rc_inc_guarded`, `emit_rc_dec`, `emit_rc_dec_guarded`, `heap_load`, `heap_store`, `compute_last_uses`, `is_mixed_adt` are the per-call-site primitives that submodules under `compiler::` reach for. Backend's internal CLIF generation calls them; no external consumer should. PFR — internal-but-exposed.
- `exe::generate_startup_object` (Row 12) — produces the tiny `_main`-exporting `.o` consumed by the system linker in `--link` mode. Called by `int::link_by_name` (not backend codegen). PFR — link-orchestration assist. Documented as part of the `--link` entry-point exception narrative in §"Object file contract" above.

### `jit::Jit` method-set (Row 9)

`Jit` is named in §"Jit — the JIT retention newtype" above as the lifecycle newtype. Its method set per the as-built public-api is broader than the as-designed §"Jit" minimal surface (just `new` + `module()`). Per Row 9 — the facade widens to document the current methods as internal-but-exposed:

- `Jit::new`, `Jit::new_with_symbols`, `Jit::new_with_isa` — three constructors (default JIT, JIT with extra extern symbols pre-registered, JIT with a caller-supplied `TargetIsa` + extra symbols). `new_with_symbols` is the dominant call-site; `new_with_isa` is used when an outer driver pre-builds the ISA to share across JITs.
- `Jit::build_shared_isa` — static entry point for the shared-ISA setup pattern. Returns `Arc<dyn TargetIsa>` for sharing across multiple `Jit::new_with_isa` calls.
- `Jit::declare_intrinsics` — declares all intrinsic externs in the JIT module before user-fn compilation. Returns `IntrinsicIds`.
- `Jit::declare_functions`, `Jit::declare_functions_prefixed` — declare the workspace's user functions in the JIT module (`Linkage::Local`, bare names; prefixed variant is for prefix-mangled multi-module batches).
- `Jit::declare_imported_functions` — declare imports as `Linkage::Import` for GOT-indirect cross-module calls.
- `Jit::compile_defn` — compile one `Defn` in the JIT module given a `CompileContext`. Returns `CompileArtifacts` (clif_ir + code_size + disasm). Called from inside `compile_to_module`'s per-symbol loop.
- `Jit::finalize`, `Jit::finalize_and_get_ptr`, `Jit::get_finalized_ptr`, `Jit::get_ptr_by_name` — finalisation and per-symbol pointer extraction. Post-finalize the JIT pages are immutable executable code.
- `Jit::jit_module()` — `&mut JITModule` accessor (the underlying Cranelift JIT). Used by callers that need to do a Cranelift-direct operation that `Jit` doesn't wrap.
- `Jit::build_compile_context` — convenience constructor for `CompileContext` bound to this `Jit`'s intrinsic `FuncId`s.
- `Jit::drop` — custom `Drop` implementation per Decision 31. Public via the trait, not a freestanding fn.
- `jit::build_isa`, `jit::declare_intrinsics_generic`, `jit::intrinsic_symbols`, `jit::jit_free_memory_call_count` — module-level free functions. `build_isa` is the freestanding ISA constructor used in the JIT path (mirrors `cache::object::build_isa` for the object path; the two have different `is_pic` defaults). `declare_intrinsics_generic<M: Module>` is the cross-module-impl helper that lets `Jit::declare_intrinsics` and the object-path declaration share one body. `intrinsic_symbols()` returns the full table of `IntrinsicSymbol { name, ptr, param_count, is_runtime, has_return }` records for JIT setup. `jit_free_memory_call_count()` returns a debug counter for Decision 31 reclaim observation (used by RC trace tests).

### `jit` shape DTOs (Row 15)

- `IntrinsicSymbol` — JIT setup record: `{ name: &'static str, ptr: *const u8, param_count: usize, is_runtime: bool, has_return: bool }`. Backend-internal — populated from `cranelisp-intrinsics` + `cranelisp-primitives` symbol tables at session init.
- `IntrinsicFuncIds` — post-declare `FuncId` lookup table per intrinsic. Returned from `declare_intrinsics_generic`. Used in CLIF emission to reference declared intrinsics.
- `IntrinsicIds` — slimmer `IntrinsicFuncIds`-like record returned from `Jit::declare_intrinsics` (non-Option fields — every intrinsic is unconditionally declared in JIT setup).
- `CompileArtifacts` — return type of `Jit::compile_defn` — `{ clif_ir, code_size, disasm }`. Wrapped into `Introspection` by the caller post-Decision-38.

PFR — internal-but-exposed. The S67 close direction is "names backend's chosen codegen toolchain"; these DTOs are part of that internal surface. Future re-shape may consolidate `IntrinsicFuncIds` + `IntrinsicIds` into one type, but that is Wave 4+ cleanup, not S67 close scope.

### `CodeFinalizer` trait + impls (Row 13)

Per Decision 38 — the trait is the surface that abstracts the JIT-vs-Object-Module finalisation step. The body's three methods `define_module_got_data`, `finalize_for_code_read`, `try_get_finalized_function` are the Cranelift-side adapters that `compile_to_module` calls via the `M: Module + CodeFinalizer` bound. The two impls — on `JITModule` (in-memory finalise + read) and `ObjectModule` (no-op finalise + `None` from `try_get_finalized_function`) — make the same call-site work in both modes.

`CodeFinalizer` is public because `compile_to_module`'s bound `M: Module + CodeFinalizer` names the trait at the public boundary. PFR.

### `CompilationResult` + `FunctionArtifacts` (Rows 2 + 15 transitional)

The as-designed §"Return shapes" target post-D41 is `Result<(), CompilationError>` for `compile_to_module` (direct-write semantics; no return tuple). The as-built signature today still returns `Result<CompilationResult, CranelispError>` where `CompilationResult { artifacts: HashMap<Symbol, FunctionArtifacts>, code_ptrs: HashMap<Symbol, *const u8>, entry_func_id, func_arities, func_ids, warnings: Vec<Warning> }` is the per-batch return tuple, and `FunctionArtifacts { clif_ir, code_size, disasm }` is the per-fn introspection record before it's split out into `Introspection`. (The `Warning` type is re-used from `cranelisp-types::error::Warning` — see `facades/types.md` §"Errors and warnings"; backend forwards diagnostic warnings produced during CLIF emission through this field.)

These types are PFR for the transitional window — the as-designed target removes them, but the migration to per-symbol direct-write `Result<(), CompilationError>` (Decision 41 close-out) lands at Wave 3 `/dev (backend)`. Until then, the as-built types are named here so the compliance test does not flag them.

Wave 3 retirement target: delete `CompilationResult` + `FunctionArtifacts` after `compile_to_module`'s per-symbol direct-write rewrite. The introspection bookkeeping migrates to writes into `int`'s `DashMap<FQSymbol, Introspection>`.

### `primitives_inline` (Rows 7 + 6)

- `primitives_inline::is_known_builtin(name: &str) -> bool` — name-keyed predicate that gates the inline-substitution lookup at backend call-sites. PFR — internal but `pub` for codegen-site call. Per §"Operator special-casing is forbidden" — the predicate is name-keyed only (no `(TraitName, Symbol, TypeName)` triples).
- `primitives_inline::try_emit_inline_primitive` — the actual emitter. Takes a `FunctionBuilder<'_>` + name + arg `Value`s + span + module + optional `panic_func_id` and returns `Option<Result<Value, CranelispError>>` (None = name didn't match, Some = either emitted or failed). PFR.
- `primitives_inline::primitive_for_trait_method(TraitName, Symbol, TypeName) -> Option<&'static str>` — **PIF — D43 forbidden pattern; Wave 3 deletion target.** Per §"Operator special-casing is forbidden" — backend MUST NOT carry `(trait, method, type)` triples. This fn is the residue from S66 close and is named in the public surface only so the compliance test does not flag it as an unknown orphan; Wave 3 `/dev (backend)` deletes the fn body + the pub signature. Tracked by FIXME 0150 (`runtime-split-primitives-intrinsics`).

### `primitives_inline.rs` retirement narrative (Row 7 + D43 full close)

`primitives_inline.rs` itself is the post-rename successor to the deleted `operators.rs` (S66 rename confirmed). Per D43 full close, the file retires fully once every Ring 0 primitive is reachable through the standard GOT-indirect call path (per the synthetic `primitives` module's `ModuleEntry::Def`s with their fn-ptr slots). The inline substitution that lives in `primitives_inline.rs` today is the code-size + dispatch-cost optimisation; it remains a legitimate substitution but must be reframed as a name-keyed shortcut over the standard path (not a parallel dispatch). Wave 3 `/dev (backend)` closes FIXME 0150 by ensuring every primitive can be called via the GOT-indirect path, then the inline-substitution table becomes an optional optimisation that can be retired without breaking call sites.

Wave 3 `/dev (backend)` is responsible for the full physical retirement; the facade narrative here reflects the D43 full-close target.

---

## PIF prep — Wave 3 targets

The remaining gaps between as-designed (the §"Free functions" + §"Errors" + §"Return shapes" sections above) and as-built (the §"Internal-but-exposed surface" §"CompilationResult + FunctionArtifacts" entry) are PIF — push implementation to match the facade. Wave 3 `/dev (backend)` is the implementing agent. The targets:

1. **Row 1 — `Code` enum location**. `Code` MUST live in `cranelisp-backend::code` (a `code.rs` module to be added in Wave 3). Currently it lives in `src/code.rs` (the `int` binary's source tree). Facade §"`Code` — the per-symbol lifecycle owner" describes the target. (D41/D35 close — already shaped by /arch W0 in `error.rs` + `artefact.rs`; `code.rs` is the remaining sibling W3 lands.)

2. **Row 2 — `compile_to_module` return shape**. Today returns `Result<CompilationResult, CranelispError>`. Target: `Result<(), CompilationError>` with direct writes to `int`'s shared stores via Decision 38's `write_code` + per-symbol `got().store_slot`. (D41 close.)

3. **Row 3 — `load_object` shape**. Today the `Linker::load_object` method exists at `cache::linker::Linker::load_object(&mut self, module_name, bytes) -> Result<(), CranelispError>`. Target: a free function `cranelisp_backend::load_object(module, object, symbol_tables) -> Result<LinkerArtefact, CranelispError>` that owns Linker construction and returns the artefact. The `Linker::load_object` method becomes `pub(crate)`. (D41 close.)

4. **Row 4 — `compile_to_object` as free function**. Today the object-codegen path is internal scaffolding. Target: a free function `cranelisp_backend::compile_to_object(module, symbol_tables) -> Result<ObjectArtefact, CranelispError>` that wraps the object-mode `compile_to_module` call and packages the `.o` + sidecar. (D41 close.)

5. **Row 5 — `Linker::get_symbol` return type**. Today returns `Option<*const u8>`. Target: `Result<*const u8, LinkerError>`. The typed error lives in `crates/cranelisp-backend/src/error.rs` (W0). (D37 close.)

6. **Row 6 — `primitive_for_trait_method` deletion**. Per §"`primitives_inline`" above — Wave 3 deletes the fn body + the pub signature. (D43 forbidden pattern residue.)

7. **Row 7 — `primitives_inline.rs` retirement / D43 full close**. Per §"`primitives_inline.rs` retirement narrative" — full close lands when every Ring 0 primitive is reachable via the standard GOT-indirect path. Closes FIXME 0150.

8. **FQTypeName migration (1 PIF row)**. The `primitives_inline` boundary takes `&TypeName` today (per `primitive_for_trait_method` row above). Once that fn deletes per Row 6, the `&TypeName` boundary disappears with it. Per Decision 0047 — FQTypeName is binding at resolved-stage boundaries; the `primitive_for_trait_method` site is one of the few backend sites that named the older `TypeName` non-FQ type. Closure of Row 6 closes the FQTypeName migration on the backend side; FIXME 0151 closes at S67 W5 acceptance per Decision 0047.

### REV-5 audit (backend consumers of `cranelisp_op_*`)

Audit task per the Wave 1 brief: grep `crates/cranelisp-backend/src/` for `cranelisp_op_` consumers.

**Result: 20 hits — NOT all-clear for D43-driven deletion.**

- `crates/cranelisp-backend/src/jit.rs:150-159` — 10 entries in `intrinsic_symbols()` registering `cranelisp_intrinsics::ops::cranelisp_op_{add,sub,mul,div,eq,neq,lt,gt,le,ge}` as JIT-mode intrinsics with name strings `"cranelisp_op_add"` etc.
- `crates/cranelisp-backend/src/compiler/literals.rs:325-339` — 10 rows in `operator_extern_name(name: &Symbol) -> Option<&'static str>` mapping operator Symbols (`"+"`, `"-"`, `"*"`, ...) to the `cranelisp_op_*` extern name strings, consumed by `compile_operator_as_value` (operator-as-value emission per spec §7.6).

**Implication.** Backend's `compile_operator_as_value` path actively names + relocates against the `cranelisp_op_*` symbols at codegen. The intrinsics-side ops crate (`cranelisp-intrinsics::ops`) cannot be deleted in isolation — backend has to migrate first.

Migration plan (Wave 3 sequencing):

a. Add `ModuleEntry::Def` entries in the synthetic `primitives` module for the 10 operators (already part of the `ring0_primitives()` body per the FIXME 0150 narrative; the entries seed at session init in `cranelisp-primitives`/typecheck).

b. Backend's `compile_operator_as_value` switches from `cranelisp_op_*` extern-relocation to GOT-indirect resolution against the primitives-module GOT slot. The wrapper-closure shape is unchanged; only the load mechanism shifts (declare-Import + extern-name → load GOT-base + offset).

c. `jit::intrinsic_symbols()` drops the 10 `cranelisp_op_*` registration rows. The intrinsic-symbols table shrinks by 10 entries; JIT setup time drops correspondingly.

d. Only after (a)-(c) land can `cranelisp_intrinsics::ops::*` delete safely. The order matters: deleting intrinsics first crashes backend codegen at the next call site.

**FIXME filed.** Per the Wave 1 brief — "if hits exist, file FIXME for /dev to migrate". Filed `design/arch/fixmes/0183-backend-migrate-cranelisp-op-extern-to-got-indirect.md` to track the Wave 3 sequencing.

---

## Non-goals / forbidden patterns

These are patterns the backend MUST NOT carry. They are listed here so `/review` (narrow backend) can flag any regression and `/dev` knows what NOT to add. Drift away from these constitutes a public-API gating concern even when no signature changes.

### Operator special-casing is forbidden

Backend MUST NOT carry name-keyed special cases for operators or any other primitive. The pre-D43 shape — a dispatch table in `backend/operators.rs` keyed on Symbol strings like `not`, `+`, `=`, `add-i64`, `eq-f64`, with inline Cranelift emission per-operator — is the **wrong shape** and is to be eliminated. Per Decision 43 (Decision 14 retracted; Decision 15 reframed) + Principle 17 + the user-arbitrated direction of 2026-05-13:

**Every primitive — including `not`, `+`, `=`, the 18 arithmetic and comparison operators in `ring0_primitives()`, and any future primitive — MUST go through the same dispatch path as any user-defined function.** That path is:

1. The `primitives` synthetic module's `SymbolTable` carries a `ModuleEntry::Def { kind: DefKind::Primitive { primitive_kind: Builtin }, got_slot: Some(slot), code: None, … }` entry per primitive (seeded by `cranelisp-primitives` at session init; see `facades/primitives.md`).
2. Backend's codegen for a call site, having resolved the callee FQ to the primitives module, looks up the entry, reads the GOT slot, and emits a standard GOT-indirect call — identical in shape to a call to any user function.
3. Inline-substitution at the codegen site (the legitimate optimisation) is keyed on Symbol ONLY (never on `(TraitName, Symbol, TypeName)` triples — backend has no trait knowledge), and is a substitution applied to the same call shape, not a parallel dispatch path. Per `facades/backend.md` §"Consumed surface" — `cranelisp-primitives` provides the substitution table; backend matches by name and emits inline Cranelift IR for the matched ones, falling through to the GOT-indirect call for the rest. The substitution is OPTIONAL — the named primitive fn ptr in the synthetic `primitives` module's GOT is always a legitimate target for indirect calls (operator-as-value, mappable-path resolutions like `(let [f =] (f 1 2))`).

**What is forbidden, concretely:**

- A dispatch function whose body is `match name { "not" => …, "add-i64" => …, "eq-f64" => …, _ => … }` operating in any path other than the name-keyed inline-substitution lookup described above. The current `crates/cranelisp-backend/src/operators.rs::emit_builtin_op` is exactly this shape and is to be deleted (see next paragraph).
- A typecheck-side or backend-side hack that treats `not` as a primitive without a `ModuleEntry::Def` in `primitives`. Per `design/typecheck/wave-3a-check-form.md` §8 + FIXME 0150: `not` failing to resolve under Principle 17 because it has no symbol-table entry is a defect — `not` must be seeded into `primitives` like every other operator.
- A code path that resolves `(+ a b)` differently from `(my-fn a b)` at the codegen layer. The typecheck-side `ResolvedCall::TraitMethod` shape (per `facades/typecheck.md` invariant 5) names the resolved primitive; backend takes that name and dispatches uniformly.

**`crates/cranelisp-backend/src/operators.rs` is scheduled for deletion in Wave 4 (D43 close).** The 531-line file is the entire body of the forbidden pattern: `match name { "add-i64" => …, "not" => …, … }` over the 19 Ring 0 primitives, doubling as both the inline-substitution table and the only emission path. Its inline-substitution role moves to `crates/cranelisp-backend/src/primitives_inline.rs` (Decision 43 — name-keyed substitution table that complements, not replaces, the GOT-indirect emission); its operator-dispatch role disappears entirely (every primitive becomes a `ModuleEntry::Def` in `primitives` and is called through the standard path). The facade text alone is the deliverable for this Wave 3a-β cycle; the file deletion lands in Wave 4 alongside the rest of D43's close-out. See FIXME 0150 (`runtime-split-primitives-intrinsics`) and the new FIXME filed by this `/arch` cycle for the explicit deletion tracking.

---

## Object file contract — what `compile_to_object` emits and `load_object` / system `ld` consume

The `.o` file is a single artefact consumed by **both** JIT mode (via `Linker::load_object` on cache hit) AND `--link` mode (via the system linker). The contract is one file, two readers — the two-GOT model in Decision 23 distinguishes which GOT is consulted at finalize, NOT where the `.o` lives.

### Format

Native host platform — Mach-O on macOS, ELF on Linux, COFF on Windows. Cranelift's `ObjectModule` produces the standard format for the configured `target_isa`.

### Function symbol naming + linkage (Decision 36)

Every user-defined function compiled by `compile_to_module` / `compile_to_object` is declared with:

- **Bare symbol name** — the function's `Symbol`, NOT module-qualified. Two modules may define functions with the same bare name; collisions across `.o` files are physically impossible because the names are `.o`-local (next bullet).
- **`Linkage::Local`** — visible inside the `.o` for intra-`.o` relocations (notably the `.o` data section GOT slot initialisers); invisible to cross-`.o` resolution. The system linker (`ld` in `--link` mode) does not see user functions in its dynamic symbol table.

Why bare + Local is sufficient: all inter-module function calls go through the per-module GOT data symbol (next section). The native code emitted for a call site does not reference the callee's function symbol — it references `__cranelisp_got_{module}` and indexes by slot. User function symbols exist only as relocation targets within the `.o` data section GOT initialisers; nothing across `.o` boundaries ever takes their address.

### GOT data symbol (Decision 23)

Per module `M`, the `.o` defines a data symbol named `__cranelisp_got_{M}` with `Linkage::Export`. Initialiser: a sequence of relocations against the local function symbols, ordered by `SymbolTable[M].symbols[name].got_slot`.

In `--link` mode: system `ld` resolves cross-module call sites by patching the data symbol; load-time, the data symbol IS the GOT.

In JIT mode: `compile_to_module` emits the SAME byte-identical CLIF — `global_value` references against `__cranelisp_got_{M}`. At finalize, the JIT's `symbol_lookup_fn` (set up by `int`) returns the in-memory `SymbolTable[M].got.base_ptr()` — the `.o` data symbol is irrelevant in JIT mode because the `Module` impl supplies a different resolution. The two paths produce different GOT bases for the same data-symbol name.

### Sidecar (`.meta.json`)

Produced by `compile_to_object` alongside the `.o`. Contains the serialised `SymbolTable<(), ()>` per Decision 25 — types, schemes, AST bodies, GOT slot layout, structural decls, `schema_version` per Decision 34. Loaded by `int`'s `ObjectCache::lookup_sidecar` in the cache-hit-typecheck path; deserialised SymbolTable is installed verbatim, skipping the form-by-form typecheck loop.

### `--link` entry point exception

The `--link` mode produces a system-linked executable. The system linker requires `_main` as `Linkage::Export`. Backend does NOT emit this alias — it's `int::link_by_name`'s job to emit a tiny additional `.o` that exports `_main` as a relocation against `__cranelisp_got_{entry_module}` at the entry module's `main` GOT slot. Backend's contract stays uniform: bare-Local for every function, including `main`. (See `facades/int.md` "Link orchestration".)

### Pairing invariant

For any module `M`, the cache stores BOTH `M.meta.json` (sidecar) AND `M.o` (object). `int`'s cache-hit path in `exec-flow-compilation` assumes pairing — sidecar present implies `.o` present. If only one exists (corrupted cache), treat as cache miss and fall through to fresh build.

---

## Types originated here

Per Principle 15 — the following are backend-originated (only `int` consumes them downstream of backend) and live in `cranelisp-backend`:

- `Code` (per Decision 41 — moves here from `src/code.rs` at Wave 3 `/dev (backend)`; the as-designed home is `cranelisp-backend::code`)
- `CompilationError` (see §"Errors" above) — `crates/cranelisp-backend/src/error.rs`, W0
- `LinkerError` (see §"Errors" above) — `crates/cranelisp-backend/src/error.rs`, W0. **Per Decision 0047 + S67 Wave 0 user-arbitrated direction, the canonical home is `cranelisp-backend` (single-consumer per Principle 15 at the backend↔int boundary).** The legacy `cranelisp-types/src/error.rs::LinkerError` row remains as a transitional duplicate; Wave 3 `/dev (backend)` + `/dev (types)` reconcile to a single home via the `cranelisp_backend::LinkerError` re-export. Pre-W0 wording (now superseded): "defined in `cranelisp-types`" — the W0 authoring of `crates/cranelisp-backend/src/error.rs` moves the canonical home to backend.
- `LinkerArtefact`, `ObjectArtefact` (see §"Return shapes" above) — `crates/cranelisp-backend/src/artefact.rs`, W0.
- `GotEvent`, `GotEventTag`, `GotProvenance`, `GotObserver` (see §"GOT-population observation")
- `register_got_observer` free function

The multi-consumer types backend depends on (`SymbolTable`, `ModuleEntry`, `DefKind`, `Type`, `Scheme`, `Symbol`, `FQSymbol`, `ModuleFullPath`, `CranelispError`, `ResolvedCall`, `MethodResolutions`, `MonoDefn`, `OverloadVariant`, `ConstrainedFn`, `TypeDefInfo`, `ConstructorInfo`, `FieldInfo`, `Expr`, `Pattern`, `MatchArm`, `Defn`, `Span`, `Visibility`, `PrimitiveDef`, `PrimitiveKind`, `SchedulingClass`, `HeapCategory`, `HeapHeader`, `NULLARY_TAG_THRESHOLD`, `CallGraph`, `CallEdge`, `CompileContext`, `CompileResult`, `GotTable`, `GOT_TABLE_SIZE`, marshaling tags) live in `cranelisp-types`. Consumers import them from there directly.

No re-exports of `cranelisp-types` items per Principle 15. Third-party re-exports (`cranelift_module`, `cranelift_object`, `cranelift::codegen::isa::TargetIsa`, `build_isa`) are out of scope of Principle 15 — they expose backend's chosen codegen toolchain; tracked separately if encapsulation becomes warranted.

---

## Consumed surface

The backend imports from:

- **`cranelisp-types`** — the full set above plus internals: `Expr`, `Pattern`, `MatchArm`, `Defn`, `Span`, `Visibility`, `ConstrainedFn`, `MonoDefn`, `OverloadVariant`, `TypeDefInfo`, `ConstructorInfo`, `FieldInfo`.

- **`cranelisp-intrinsics`** — backend emits Cranelift IR that calls intrinsic extern functions (per Decision 43, the post-split home of all backend-emitted-call targets). Not a code dependency in the Rust sense (backend doesn't `use cranelisp_intrinsics::*`) but a relocation-time dependency: the JIT registers intrinsic fn pointers via `JITBuilder::symbol`, and the `.o` files contain unresolved relocations against intrinsic symbol names that `--link`'s system linker resolves against the `cranelisp-intrinsics` archive. Backend names the intrinsic symbols by string at codegen time:
  - `cranelisp_alloc`, `heap_alloc_payload`, `heap_dealloc`
  - `rc_underflow_check`, `rc_inc`, `rc_dec`
  - `consume_shallow`, `dec_shallow_io`, per-type drop glue (backend-emitted, named in the `.o`)
  - `vec_new`, `vec_len`, `vec_set_copy`, `vec_push_copy`, `vec_push_grow`, `vec_drop`
  - `heap_alloc_string`, `string_read`
  - `sconcat`, `quote_sexp`
  - `cranelisp_run_io`, `io_run`, `run_io_trampoline`
  - `ivar_create`, `ivar_spark`, `ivar_force`
  - `runtime_panic`

- **`cranelisp-primitives`** — for the inline-substitution table at backend's direct call sites (per Decision 43). The substitution table is keyed on `Symbol` (e.g., `add-i64`, `int-to-string`) ONLY — never on `(TraitName, Symbol, TypeName)` triples. Trait dispatch resolves at typecheck/stdlib level; the resolved target name is what backend sees. Backend has no trait knowledge per Decision 43 (Decision 14 retracted; Decision 15 reframed). The substitution table lives in `cranelisp-backend/src/primitives_inline.rs` (renamed from `operators.rs` per Decision 43); it is name-keyed only. Substitution is optional — the named primitive fn ptr in the synthetic `primitives` module's GOT is a legitimate fallback for indirect calls (operator-as-value, GOT-indirect cross-module calls). Backend names primitives by string at codegen time when emitting non-substituted calls (e.g., `add-i64`, `int-to-string`, `parse-int`, `float-to-string`, `bool-to-string`); registration of primitive fn ptrs happens at `int`'s session init.

- **Cranelift** (`cranelift`, `cranelift-codegen`, `cranelift-jit`, `cranelift-module`, `cranelift-frontend`, `cranelift-object`) — direct dependencies. Backend is the only crate that names Cranelift types.

The backend does NOT import from `cranelisp-frontend`, `cranelisp-typecheck`, `cranelisp-platform`, `cranelisp-runtime` (retired per Decision 43), or `cranelisp` (binary). All inputs flow via `cranelisp-types` plus the relocation-time bindings against `cranelisp-intrinsics` + `cranelisp-primitives`.

---

## Sealed traits

None implemented. Backend does not implement traits from `cranelisp-types`. (`Module` is from the `cranelift-module` crate, not from `cranelisp-types`.)

---

## `#[non_exhaustive]` DTOs

`LinkerArtefact`, `ObjectArtefact`, `Code`, `CompilationError`, `GotEvent`, `GotEventTag`, `GotProvenance` are all `#[non_exhaustive]`. `Jit`, `Linker` are opaque structs (no public field access). Per Decision 41 (S66 amendment + rollback), `compile_to_module` no longer returns a `JitArtefact` — it writes `Code::Jit(Arc<Jit>)` directly via `write_code` and writes the fn pointer to the entry's GOT slot via `got().store_slot`, then returns `Result<(), CompilationError>`. Types re-exported from `cranelisp-types` are `#[non_exhaustive]` per the types-crate facade.

---

## Bounded-context invariants

These hold across sprints — the contract `cranelisp-backend` makes with the rest of the workspace:

1. **Single compilation entry point per mode.** Per Decision 23 — `compile_to_module<M: Module>` is the sole CLIF emission path. Object vs JIT differs only in the `Module` instance the integration layer supplies; CLIF emission is byte-identical. Mode is NOT a function parameter.

2. **Uniform consuming calling convention.** Per Decision 24 — every call site emits identically for RC management. Caller transfers ownership of heap-typed args (inc-before-call for non-last-use, direct transfer for last-use); callee owns heap params. Data constructors, user fns, trait methods, builtins, and externs all follow the same rule. There is no "borrowing" classification.

3. **Compiled code lifecycle owner lives on `ModuleEntry::Def.code`; fn ptr lives in `SymbolTable.got()`, indexed by `ModuleEntry::Def.got_slot`.** Per Decisions 25 + 41 (S66 amendment + rollback `1dc57ae`) — backend constructs `Code::Jit(Arc<Jit>)` directly (Decision 35 Layer 2 Option B retracted by Decision 41) and writes via Decision 38's `write_code(&self, sym, code)` (interior-mutable; no `&mut` flow); backend additionally writes the resulting fn pointer to the entry's GOT slot via `symbol_table.got().store_slot(slot, ptr)`. The GOT is the **single source of truth** for callable addresses; the briefly-considered sibling `fn_ptr` field (commit `b09ec76`) was rolled back the same day as redundant. `Code` carries lifecycle ownership ONLY — the variants no longer embed a `ptr`. The `Code` enum lives in `cranelisp-backend/src/code.rs` (moved from `src/code.rs` per Decision 41). For non-codegen crates the field's type stays `Option<C>` for any `C: CodeStore`; backend's signatures use `SymbolTable<Code, ()>` per Decision 41, while frontend/typecheck stay generic on `SymbolTable<(), ()>` per Decision 32. `load_object` returns a `LinkerArtefact` for cache-hit code; `compile_to_object` returns an `ObjectArtefact` for nice-worker output. There is no `JitArtefact` return shape post-Decision-41 — direct writes replace the previous tuple-return.

4. **`defined_symbols()` is the codegen-compilable predicate.** Per Decision 22 — `compile_to_module` trusts the contract: if a name in `names` resolves to an entry where `defined_symbols()` would not include it, return `Err(CodegenError)` rather than synthesising. One filter, exposed on `SymbolTable`, consumed identically by callers and the backend's internal loop.

5. **Decision 31 reclaim safety.** Custom `Drop for Jit` calls `unsafe JITModule::free_memory()`. The safety invariant — "no derived fn pointer reachable when refcount hits 0" — is upheld by: (a) every derivative pointer lives on a `ModuleEntry::Def.code` (the Arc keeps the Jit alive), (b) GOT slots are atomic-swapped on REPL redefinition before the old Arc can drop, (c) language-level fn values are heap closures that dispatch through GOT, not raw code pointers. Backend does not need to enforce these; it relies on `int`'s discipline (Decisions 23, 31).

6. **Two-GOT model, one CLIF.** Per Decision 23 — same data-symbol reference (`Linkage::Import` against `__cranelisp_got_{M}`) appears in every CLIF emission. JIT mode resolves via `int`'s `JITBuilder::symbol_lookup_fn` returning `SymbolTable[M].got.base_ptr()`. `--link` mode resolves via the `.o` data section GOT defined as `Linkage::Export` per Decision 36. Backend does not branch on mode; the `Module` impl supplied at finalize determines resolution.

7. **Bare-name + Local linkage uniformly.** Per Decision 36 — every user function is `Linkage::Local` with bare-name symbol. No `user`/`main` special case. The `--link` mode `_main` alias is `int`'s job, not backend's.
