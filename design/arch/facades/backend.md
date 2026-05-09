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

- `Code` (per Decision 41 — already moved here from `cranelisp-types`)
- `CompilationError` (see §"Errors" above)
- `GotEvent`, `GotEventTag`, `GotProvenance`, `GotObserver` (see §"GOT-population observation")
- `register_got_observer` free function

`LinkerError` is the typed result of `Linker::get_symbol` (per FIXME 0154 resolution); it is **defined in `cranelisp-types`** (multi-consumer per Principle 15 — backend constructs, `int` matches at cache-hit failure) and surfaces in the backend public API via the `Linker::get_symbol` signature. See `facades/types.md` §"Errors and warnings" for the canonical definition; the §"Errors" enumeration above is the same shape repeated for facade-local readability.

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
