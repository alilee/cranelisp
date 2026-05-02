# Facade spec — `crates/cranelisp-backend/`

**Bounded context citation.** Typed AST → Cranelift IR → executable. Owns codegen, RC, JIT lifecycle, caching, and linking. Paired with runtime. See `bounded-contexts.md` §3 — Backend.

This spec is **target-stating**. Drift detection between as-designed and as-built is the job of `cargo-public-api` (M4-pending) and `/review`'s per-PR audit, not this document.

---

## Public surface (as-designed)

### Free functions — the three codegen entry points

These are the entire backend boundary used by `int`'s priority workers (JIT path) and nice workers (object path).

```rust
pub fn compile_to_module<M: Module>(
    module: &ModuleFullPath,
    names: &[Symbol],
    symbol_tables: &SymbolTables,
    jit: &mut M,
) -> Result<JitArtefact, CranelispError>;

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

`compile_to_module` is the JIT-mode entry — used by `int`'s priority workers when typecheck-cache missed. Generic over `M: cranelift_module::Module` per Decision 23 — the same body emits byte-identical CLIF whether `M` is a `JITModule` or an `ObjectModule`; the mode is a property of which `Module` instance the integration layer constructs at finalize. (See "Object file contract" below.)

`load_object` is the JIT-mode cache-hit entry — reads a `.o` produced by an earlier `compile_to_object` call (or by `--link` mode), runs the cache `Linker` to resolve each defined symbol's address, returns a `LinkerArtefact` that `int` writes into `ST[m].symbols[name].code` per Decision 35.

`compile_to_object` is the nice-worker object-codegen entry — produces the `.o` artefact + sidecar (`.meta.json` containing the serialised `SymbolTable<(), ()>`). Backend writes nothing to disk itself; `int`'s `ObjectCache::write` does the file IO.

### Return shapes

```rust
#[non_exhaustive]
pub struct JitArtefact {
    pub jit: Arc<Jit>,                                         // Decision 31 — the per-batch retention root, custom Drop reclaims via unsafe JITModule::free_memory()
    pub ptrs: HashMap<Symbol, *const u8>,                      // per-symbol code addresses for `int` to wrap as Code::Jit { jit, ptr }
}

#[non_exhaustive]
pub struct LinkerArtefact {
    pub linker: Arc<Linker>,                                   // per-module retention root for cache-hit code — analogous to Jit for JIT mode
    pub ptrs: HashMap<Symbol, *const u8>,                      // per-symbol code addresses for `int` to wrap as Code::Linker { linker, ptr }
}

#[non_exhaustive]
pub struct ObjectArtefact {
    pub object: Vec<u8>,                                       // ELF or Mach-O bytes — host-platform native
    pub sidecar: SymbolTable<(), ()>,                          // serialised SymbolTable for the cache .meta.json (no code, no linker)
}
```

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

Wrapped in `Arc<Jit>` by `compile_to_module`; the Arc lives on `ModuleEntry::Def.code = Code::Jit { jit, ptr }` per Decision 35. When the last clone drops (REPL redefinition or session shutdown), executable memory is reclaimed.

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

Wrapped in `Arc<Linker>` by `load_object`; analogous lifecycle to `Jit`. `Arc<Linker>` lives on `ModuleEntry::Def.code = Code::Linker { linker, ptr }` for cache-hit modules.

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

## Re-exports from `cranelisp-types`

```rust
pub use cranelisp_types::{
    Symbol, ModuleFullPath, FQSymbol, SymbolTable, ModuleEntry, DefKind,
    Type, Scheme, CranelispError,
    GotTable, GOT_TABLE_SIZE,
    ResolvedCall, MethodResolutions,
    PrimitiveDef, PrimitiveKind, SchedulingClass,
    HeapCategory, HeapHeader, NULLARY_TAG_THRESHOLD,
    CallGraph, CallEdge, CompileContext, CompileResult,
    TAG_SNIL, TAG_SCONS, TAG_SEXP_INT, TAG_SEXP_FLOAT, TAG_SEXP_BOOL, TAG_SEXP_STR, TAG_SEXP_SYM, TAG_SEXP_LIST, TAG_SEXP_BRACKET,
};
```

Backend re-exports types that flow through its API surface — return shapes, codegen-context types, marshaling tags consumed by emitted code.

---

## Consumed surface

The backend imports from:

- **`cranelisp-types`** — the full set above plus internals: `Expr`, `Pattern`, `MatchArm`, `Defn`, `Span`, `Visibility`, `ConstrainedFn`, `MonoDefn`, `OverloadVariant`, `TypeDefInfo`, `ConstructorInfo`, `FieldInfo`.

- **`cranelisp-runtime`** — backend emits Cranelift IR that calls runtime extern functions. Not a code dependency in the Rust sense (backend doesn't `use cranelisp_runtime::*`) but a relocation-time dependency: the JIT registers runtime fn pointers via `JITBuilder::symbol`, and the `.o` files contain unresolved relocations against runtime symbol names that `--link`'s system linker resolves against the `cranelisp-runtime` archive. Backend names the runtime symbols by string at codegen time:
  - `cranelisp_runtime::heap_alloc`, `heap_alloc_payload`, `heap_dealloc`
  - `cranelisp_runtime::rc_underflow_check`
  - `cranelisp_runtime::vec_new`, `vec_len`, `vec_set_copy`, `vec_push_copy`, `vec_push_grow`, `vec_drop`
  - `cranelisp_runtime::heap_alloc_string`, `string_read`, `alloc_string`, `read_string_as_str`
  - `cranelisp_runtime::int_to_string`, `parse_int`, `float_to_string`, `bool_to_string`
  - `cranelisp_runtime::sconcat`, `quote_sexp`
  - `cranelisp_runtime::cranelisp_run_io`, `run_io_trampoline`
  - `cranelisp_runtime::ivar_create`, `ivar_spark`, `ivar_force`
  - `cranelisp_runtime::runtime_panic`

- **Cranelift** (`cranelift`, `cranelift-codegen`, `cranelift-jit`, `cranelift-module`, `cranelift-frontend`, `cranelift-object`) — direct dependencies. Backend is the only crate that names Cranelift types.

The backend does NOT import from `cranelisp-frontend`, `cranelisp-typecheck`, `cranelisp-platform`, or `cranelisp` (binary). All inputs flow via `cranelisp-types`.

---

## Sealed traits

None implemented. Backend does not implement traits from `cranelisp-types`. (`Module` is from the `cranelift-module` crate, not from `cranelisp-types`.)

---

## `#[non_exhaustive]` DTOs

`JitArtefact`, `LinkerArtefact`, `ObjectArtefact` are all `#[non_exhaustive]`. `Jit`, `Linker` are opaque structs (no public field access). Types re-exported from `cranelisp-types` are `#[non_exhaustive]` per the types-crate facade.

---

## Bounded-context invariants

These hold across sprints — the contract `cranelisp-backend` makes with the rest of the workspace:

1. **Single compilation entry point per mode.** Per Decision 23 — `compile_to_module<M: Module>` is the sole CLIF emission path. Object vs JIT differs only in the `Module` instance the integration layer supplies; CLIF emission is byte-identical. Mode is NOT a function parameter.

2. **Uniform consuming calling convention.** Per Decision 24 — every call site emits identically for RC management. Caller transfers ownership of heap-typed args (inc-before-call for non-last-use, direct transfer for last-use); callee owns heap params. Data constructors, user fns, trait methods, builtins, and externs all follow the same rule. There is no "borrowing" classification.

3. **Compiled code lives on `ModuleEntry::Def.code`.** Per Decision 25 — backend returns artefacts (`JitArtefact`, `LinkerArtefact`, `ObjectArtefact`); `int` constructs the `Code` enum (`src/code.rs` per Decision 35) and writes it to `ModuleEntry::Def.code`. Backend never names `Code` and never directly mutates `SymbolTable.symbols[name].code` — the field's type is `Option<C>` for any `C: CodeStore`, and backend operates on `SymbolTable<(), ()>` per Decision 32.

4. **`defined_symbols()` is the codegen-compilable predicate.** Per Decision 22 — `compile_to_module` trusts the contract: if a name in `names` resolves to an entry where `defined_symbols()` would not include it, return `Err(CodegenError)` rather than synthesising. One filter, exposed on `SymbolTable`, consumed identically by callers and the backend's internal loop.

5. **Decision 31 reclaim safety.** Custom `Drop for Jit` calls `unsafe JITModule::free_memory()`. The safety invariant — "no derived fn pointer reachable when refcount hits 0" — is upheld by: (a) every derivative pointer lives on a `ModuleEntry::Def.code` (the Arc keeps the Jit alive), (b) GOT slots are atomic-swapped on REPL redefinition before the old Arc can drop, (c) language-level fn values are heap closures that dispatch through GOT, not raw code pointers. Backend does not need to enforce these; it relies on `int`'s discipline (Decisions 23, 31).

6. **Two-GOT model, one CLIF.** Per Decision 23 — same data-symbol reference (`Linkage::Import` against `__cranelisp_got_{M}`) appears in every CLIF emission. JIT mode resolves via `int`'s `JITBuilder::symbol_lookup_fn` returning `SymbolTable[M].got.base_ptr()`. `--link` mode resolves via the `.o` data section GOT defined as `Linkage::Export` per Decision 36. Backend does not branch on mode; the `Module` impl supplied at finalize determines resolution.

7. **Bare-name + Local linkage uniformly.** Per Decision 36 — every user function is `Linkage::Local` with bare-name symbol. No `user`/`main` special case. The `--link` mode `_main` alias is `int`'s job, not backend's.
