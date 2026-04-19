# Module Caching

Design for the Cranelisp reimplementation's module cache system. This covers persistent compilation artifacts, cache invalidation, object file generation, and linking for cached modules.

## 1. Problem Statement

Compiling a multi-module Cranelisp project requires processing every module through the full pipeline (reader, macro expander, AST builder, typechecker, codegen) on every invocation. For projects with stable dependencies (stdlib, shared libraries), this is wasteful -- the stdlib alone has 8+ modules that change only when the compiler changes. Module caching persists compiled artifacts to disk so unchanged modules skip compilation entirely.

### Goals

1. **Correctness**: cached code must produce identical results to freshly compiled code.
2. **Invalidation safety**: stale caches must never be served. When in doubt, recompile.
3. **REPL/batch path convergence**: the most structurally important goal. The batch and REPL compilation paths must share as much code as possible. Code volume and duplication between these paths is a primary design metric — the sketch grew them incrementally and accumulated significant divergence. The cache-hit and cache-miss paths must also share a single code path, parameterized only where unavoidable. See §8 for the unification strategy and options analysis.
4. **Three-mode support**: the cache participates in dev mode (REPL JIT), quick build mode (link cached `.o` files), and is transparent to release mode (LLVM recompile from source). Per spec C.5.3.
5. **REPL responsiveness**: cache writes must not block the REPL interaction loop.
6. **Structural cleanliness**: avoid the sketch's 21-parameter functions, duplicated ISA construction, and interleaved concerns.

### Non-goals

- Cross-machine cache sharing (caches are local to a build environment).
- Incremental compilation within a module (the module is the caching unit).
- Release mode object files (LLVM backend is a separate future crate).

## 2. Sketch Comparison

### How the sketch does it

The sketch's cache system spans three files (1,704 lines):

- **`cache.rs`** (1,069 lines): manifest management, SHA-256 source hashing, `compile_module_to_object()` to re-emit each module's functions into a Cranelift `ObjectModule`, `CacheWritePacket` for background/parallel writes, atomic file writes.
- **`cache_writer.rs`** (139 lines): background mpsc thread for REPL cache writes. Accumulates manifest updates and flushes on shutdown.
- **`linker.rs`** (496 lines): loads cached `.o` files, resolves Mach-O and ELF aarch64 relocations against the live JIT symbol table, maps code pages executable via `mmap`/`mprotect`.

The cache stores three file types per module:
- `manifest.json` -- global index mapping module paths to source hashes, plus version/triple/fingerprint metadata.
- `<module>.meta.json` -- serialized `CompiledModule` (symbol table, import specs, GOT slot assignments, etc.).
- `<module>.o` -- relocatable object file produced by `ObjectModule`.

The cache key is a SHA-256 of the module's source text, checked against the manifest. A binary fingerprint (mtime of the compiler executable) invalidates all caches when the compiler is rebuilt.

On cache hit, `try_load_cached_module()` deserializes the `.meta.json`, loads the `.o` through the linker, reinstalls import scopes, macros, overloads, and trait methods into the live session.

### What worked

1. **Module-granular caching**: the module as caching unit matches the compilation unit (spec 8.10.3), making invalidation straightforward.
2. **Background write thread**: the REPL returns immediately after JIT compilation; cache writes happen asynchronously on a dedicated thread.
3. **Atomic file writes**: temp-file-then-rename prevents readers from seeing partial writes.
4. **Manifest-based invalidation**: a single manifest file provides O(1) cache-hit checks without reading every module's metadata.
5. **ObjectModule for `.o` generation**: Cranelift's `ObjectModule` produces standard relocatable objects that a system linker could also consume.

### What the audit found (15 findings)

The cache audit (`sketch/audits/cache.md`) identified 3 HIGH, 7 MEDIUM, and 5 LOW findings:

| ID | Severity | Issue |
|---|---|---|
| HIGH-1 | Resolved | RC/trace intrinsics not declared in ObjectModule (was a divergence risk) |
| HIGH-2 | High | Duplicate ISA construction diverges from JIT path |
| HIGH-3 | High | `compile_module_to_object()` has 21 positional parameters |
| MED-1 | Medium | `write_module_cache()` is dead code |
| MED-2 | Medium | `try_load_cached_module()` 238 lines, duplicated import resolution |
| MED-3 | Medium | Silent failure of cache writes |
| MED-4 | Medium | Linker GOT is a fixed 512-entry table with panic on overflow |
| MED-5 | Medium | Binary fingerprint uses mtime, not content hash |
| MED-6 | Medium | Triple compatibility check uses string containment |
| MED-7 | Medium | `extract_cache_inputs` is O(n) per module |
| LOW-1 | Low | `fn_slots_snapshot` uses unnamed tuples |
| LOW-2 | Low | `declare_imported_func` has unused `return_count` parameter |
| LOW-3 | Low | `try_load_cached_module` returns `Option<bool>` |
| LOW-4 | Low | Module filename `.` to `_` replacement has collision risk |
| LOW-5 | Low | Zero unit tests for cache, cache_writer, or linker |

### Where the reimplementation diverges

| Aspect | Sketch | Reimplementation | Rationale |
|---|---|---|---|
| **Crate ownership** | All in one crate | Cache logic in `cranelisp-backend`, pipeline wiring in `cranelisp` binary | Architecture principle 1 (decoupling). Keeps backend testable without pipeline. |
| **Persisted shape** (Phase 5 / Step 5b) | Serializes the monolithic `CompiledModule` (all symbol info, GOT slots, runtime pointers, codegen state intermingled) | `.meta.json` IS a serialised `SymbolTable<(), ()>` carrying structural decls, symbols (with `ast` bodies + `got_slot`), and `schema_version: u32`. `code` (per-function) and `platform_fn_ptr` are `#[serde(skip)]` and re-derived on cache-hit load. The `.o` file remains the per-module Cranelift `ObjectModule` output. Per Decision 25 + Decision 33 + Decision 34 + Decision 26. | Architecture Principle 7 (single source of truth — one symbol-table shape persisted; no parallel `CacheCodegenState` or `CacheMetadata` decomposed types) + Principle 8 (no interim shape — `SymbolTable` IS the §9 target so persisting it directly avoids a translator/adapter pair) + Decision 33 (structural decls live as `SymbolTable` fields; `ModuleStructure` dissolves) + Decision 34 (explicit `schema_version` makes shape mismatch a discoverable cache-stale, not a cryptic deserialise error). |
| **Schema versioning** | Implicit via `cache_format_version: u32` on `CacheMetadata` | Explicit `schema_version: u32` on the serialised `SymbolTable`; constant `CACHE_SCHEMA_VERSION` lives in `crates/cranelisp-backend/src/cache/mod.rs`. Mismatch invalidates the entry as if dependencies changed (same code path as source-mtime change). Per Decision 34. | Principle 5 (testability — version mismatches surface as a typed `CacheStale::SchemaMismatch` discriminator, not as a `serde_json::Error::Message`). |
| **`code` / `platform_fn_ptr` placement** | Bespoke `CacheCodegenState` carrying GOT slot assignments, function param counts, and reconstruction hints; runtime pointers regenerated from a separate path | `code: Option<C>` (per-function) and `platform_fn_ptr: Option<*const u8>` (per-platform-effect) live directly on `ModuleEntry::Def`, both `#[serde(skip)]`. Cache-hit load deserialises the symbol table; the priority worker re-runs codegen against the deserialised `ast` bodies to repopulate `code` (which retains a freshly-allocated `Arc<Jit>` on the entry per Decision 31 Scenario 2). Platform fn ptrs are re-resolved by re-opening the platform DLL named by the persisted `PlatformDecl` and reading its manifest (per Decision 26's serialisation discipline). | Principle 7 (one `code` location per symbol — no `CacheCodegenState` parallel store) + Decisions 25/26/31 unified — the cache deserialises into the same data shape that the priority worker writes during fresh build. |
| **ISA construction** | 3 separate ISA builds with divergent flags | Single `build_isa(is_pic: bool)` in backend | Addresses HIGH-2. Architecture principle 7 (single source of truth). |
| **Object compilation API** | 21 positional parameters | `compile_to_module<M: Module>(module_path, names, symbol_tables, module)` — single entry point per Decision 23 (parameterised over Cranelift module). After Step 5c the `symbol_tables` is `&DashMap<ModuleFullPath, SymbolTable<C, L>>`, but the backend still operates on the typecheck-product shape (`SymbolTable<(), ()>`) — see `compile-to-module.md` §17. | Addresses HIGH-3 + Decisions 23 + 32 (single compilation entry point; generic boundary erased by default `()`). |
| **Binary fingerprint** | mtime-based | mtime-based (retain sketch approach) | MED-5 considered but mtime is the pragmatic choice: a single `stat()` call vs reading and hashing a multi-MB binary on every startup. The failure mode (mtime preserved across different binaries via `cp -p` or CI caching) is rare and limited to deliberate file copying. Source files use content hashing (marginal cost since we read them anyway), but the compiler binary check must be O(1). |
| **Triple check** | String containment | Exact `target_lexicon::Triple` comparison | Addresses MED-6. |
| **Module filenames** | `.` replaced with `_` (collision risk) | URL-encode dots as `%2e` or use nested directories | Addresses LOW-4. |
| **Cache load path** | Duplicates import resolution from normal path | Shared `install_module_scope()` helper; cache-restore reads structural decls (`imports`/`exports`/`platforms`/`submodules`) from the deserialised `SymbolTable` fields (Step 5a / Decision 33), eliminating the historical "duplicate the import-resolution loop in `try_load_cached_module`" finding (MED-2). | Decision 33 + MED-2 — one resolver, two callers (fresh-build worker and cache-restore loader). |
| **Error handling** | `eprintln!` warnings, silent fallback | `Result<T, CranelispError>` throughout, with warning accumulation | Architecture principle 8 on warnings-as-data. |
| **Linker GOT** | Fixed 512-entry mmap, panic on overflow | Growable `Vec<u64>` with mprotect before use | Addresses MED-4. |
| **Test coverage** | 14 integration tests, 0 unit tests | Unit tests for pure functions (round-trip serialise/deserialise on hand-built `SymbolTable` instances; `CACHE_SCHEMA_VERSION` mismatch emits the right invalidation discriminator) + `/qa`-owned integration tests on multi-module cache scenarios. Addresses LOW-5. |

## 3. Cache Key Design

A module's cache is valid when all inputs that affect its compiled output are unchanged.

### Primary key: content hash

```
cache_key = SHA-256(source_text)
```

The source text of the `.cl` file is the primary input. This is computed once when the source is read and compared against the manifest.

### Secondary key: transitive dependency hashes

A module's compiled form depends on its imports. If module `A` imports from module `B`, and `B`'s type signatures change, `A`'s cached `.o` may call functions with different signatures or GOT layouts.

**Strategy**: the manifest stores per-module source hashes. When checking cache validity for module `A`:
1. Check `A`'s own source hash.
2. For each of `A`'s direct imports, check that the import's source hash in the manifest matches the current source.

If any dependency has changed, `A` is recompiled. This is conservative (a change to `B`'s private internals that doesn't affect its public API still invalidates `A`) but correct and simple. A future optimization could hash the public interface rather than the full source.

### Global invalidation keys

These invalidate the entire cache:

| Key | What it detects |
|---|---|
| `cache_format_version: u32` | Changes to the `.o` or `.meta.json` format |
| `compiler_mtime: u64` | mtime of the cranelisp binary (seconds since epoch). Detects compiler rebuilds. O(1) stat check. |
| `target_triple: String` | Architecture/OS. Exact match via `target_lexicon::Triple`. |
| `cranelift_version: String` | Cranelift version string. Object file format may change between versions. |

All four are stored in `manifest.json` and checked before any per-module lookup.

## 4. Serialization Format

### What is serialized

`CacheCodegenState` is the serializable subset of `ModuleCodegenState`. The architecture's four decomposed types are `SymbolTable`, `ModuleCodegenState`, `ModuleStructure`, and `CacheMetadata`. `ModuleCodegenState` contains runtime state (GOT pointer table, live code pointers) that cannot be serialized. The cache needs the *recoverable* parts of that state — GOT slot assignments, param counts, definition source/sexp/defn for REPL introspection — so that a cache-loaded module can reconstruct its `ModuleCodegenState` after linking the `.o` file.

`CacheCodegenState` is therefore a new type defined in `cranelisp-backend` (where `ModuleCodegenState` lives), deriving `Serialize + Deserialize`. It is constructed from `ModuleCodegenState` at cache-write time and consumed at cache-load time to rebuild `ModuleCodegenState` (with fresh runtime pointers from the linker). It is *not* content in `CacheMetadata` — `CacheMetadata` holds cache-management data (content hashes, dependency hashes) while `CacheCodegenState` holds codegen-recovery data (slot assignments, param counts, introspection artifacts).

The sketch serializes the entire `CompiledModule` as JSON. The reimplementation serializes the decomposed types separately:

| Component | Format | Content | Architecture type |
|---|---|---|---|
| `SymbolTable` | JSON | All `ModuleEntry` variants: Def (scheme, visibility, DefKind), Import, Reexport, TypeDef, TraitDecl, Constructor, Macro | `SymbolTable` (in `cranelisp-types`) |
| `ModuleStructure` | JSON | File path, mod decls, import specs, export specs, impl sexps, source hash | `ModuleStructure` (in `cranelisp-types`) |
| `CacheCodegenState` | JSON | GOT slot assignments, function param counts, definition source/sexp/defn for REPL introspection | Serializable subset of `ModuleCodegenState` (in `cranelisp-backend`) |
| `CacheMetadata` | JSON | Content hash, dependency hashes, cache format version | `CacheMetadata` (in `cranelisp-types`) |
| Object file | Binary `.o` | Cranelift `ObjectModule` output -- standard relocatable object | — |

The first four are combined into a single `.meta.json` and the object file is a separate `.o` file.

### Serde strategy

All types in `cranelisp-types` already derive `Serialize + Deserialize` (architecture decision). Fields that contain runtime state (function pointers, JIT handles) use `#[serde(skip)]` with defaults:

```rust
// In DefCodegen
#[serde(skip)]
pub code_ptr: Option<*const u8>,  // Reconstructed from .o on load

#[serde(skip)]
pub compile_duration: Option<std::time::Duration>,  // Not meaningful after reload
```

### Why JSON, not binary

JSON is human-inspectable, debuggable, and forward-compatible (unknown fields are silently ignored with `#[serde(default)]`). The `.meta.json` files are small (typically 1-50 KB). The performance-critical artifact is the `.o` file, which is binary. If JSON metadata becomes a bottleneck (unlikely for <100 modules), a migration to MessagePack or bincode is a localized change in the cache read/write functions.

## 5. ObjectModule vs JITModule

### The dual-compilation question

The sketch compiles each module twice when caching: once to `JITModule` for immediate execution, then again to `ObjectModule` for the `.o` file. This is because Cranelift's `JITModule` and `ObjectModule` are different consumers of `Function` objects -- a function compiled into a JIT cannot be extracted as relocatable code.

The reimplementation follows the same pattern. Alternatives considered:

1. **Serialize JIT memory directly**: rejected. JIT code contains absolute addresses (function pointers, GOT base) that are process-specific. Relocatable objects are necessary for loading at different addresses.

2. **Compile to ObjectModule only, then load via linker**: would avoid double compilation but adds linking latency to every REPL expression. The JIT path exists for <10ms interactive latency (spec C.6.1).

3. **Compile to ObjectModule, extract code and relocations, fixup addresses in-process**: this is essentially what the linker does when loading cached `.o` files. Would unify the paths but means the REPL always goes through the linker, which is slower than JIT for single expressions.

**Decision**: keep dual compilation. The JIT path serves interactive latency. The ObjectModule path runs on a background thread (or rayon pool) and writes the `.o` asynchronously. The cost is paid once per module change, not on every REPL expression.

### GotReference::DataSymbol

The sketch's `GotReference` enum has two variants:

```rust
enum GotReference {
    Immediate(usize),  // JIT: absolute address of GOT table in memory
    DataSymbol(DataId), // ObjectModule: symbolic reference resolved at link time
}
```

The reimplementation retains this pattern. In the JIT path, `GotReference::Immediate` embeds the GOT base address directly into generated code. In the ObjectModule path, `GotReference::DataSymbol` emits a data symbol reference that the linker resolves when loading the `.o`.

This is the correct abstraction: the `FnCompiler` doesn't know which consumer it's targeting. It loads the GOT base from whatever `GotReference` provides. The Immediate variant becomes a constant load; the DataSymbol variant becomes a relocation.

**Crate placement**: `GotReference` lives in `cranelisp-backend` since it references `cranelift_module::DataId`.

## 6. Cache Invalidation Strategy

### When to invalidate

| Trigger | Scope | Detection |
|---|---|---|
| Source file changed | Single module + dependents | SHA-256 hash mismatch in manifest |
| Dependency changed | Importing module | Transitive dependency hash check (section 3) |
| Compiler rebuilt | All modules | `compiler_hash` mismatch in manifest |
| Cache format version bumped | All modules | `cache_format_version` mismatch |
| Target architecture changed | All modules | `target_triple` mismatch |
| Cranelift version changed | All modules | `cranelift_version` mismatch |

### When NOT to invalidate

- `.cl` file touched but content unchanged (hash is content-based, not mtime-based).
- Unrelated module changed (each module's hash is independent).
- Cache directory manually inspected or copied (content hashes are self-validating).

### Invalidation is conservative

If any validation check fails, the module is recompiled. There is no "partial cache hit" -- either the full metadata + object file are valid, or the module is compiled from scratch. This simplifies reasoning: a cache hit means "this module's output is byte-identical to what a fresh compile would produce."

## 7. Background Writing

### Approach

The reimplementation adopts the sketch's background writer pattern with structural improvements.

In the REPL, after JIT compilation succeeds:
1. A `CacheWritePacket` is built, capturing all data needed for ObjectModule compilation as owned values (no borrowed pointers, no raw pointers -- fully `Send`).
2. The packet is sent to a background writer thread via `mpsc::Sender`.
3. The REPL returns immediately to the user.
4. The background thread compiles the ObjectModule, writes `.meta.json` and `.o`, and accumulates manifest updates.
5. On REPL shutdown, the background thread flushes pending writes and writes the final manifest.

In batch mode, cache writes happen after the full compilation loop completes, using rayon's `par_iter` to compile ObjectModules in parallel. This is because monomorphisation may generate specializations that land in earlier modules' GOT tables, so all modules must be fully compiled before any cache packets are built.

### CacheWritePacket design

The sketch's packet has 16 fields, several of which are redundant snapshots of session-wide data. The reimplementation structures the packet around the decomposed types:

```rust
/// Owned snapshot for background cache writing. Fully Send-safe.
pub struct CacheWritePacket {
    // Identity
    pub cache_dir: PathBuf,
    pub module_path: ModuleFullPath,
    pub source_hash: String,
    pub is_stdlib: bool,

    // Serialized metadata (pre-computed on the sending thread)
    pub meta_json_bytes: Vec<u8>,

    // Inputs for ObjectModule compilation
    pub object_compile_input: ObjectCompileInput,
}

/// All inputs needed to compile a module to an ObjectModule.
/// Grouped to replace the sketch's 21 positional parameters.
pub struct ObjectCompileInput {
    pub module_path: ModuleFullPath,
    pub defns: Vec<(Defn, Scheme)>,
    pub method_resolutions: MethodResolutions,
    pub fn_slot_assignments: HashMap<Symbol, FnSlotInfo>,
    pub fn_to_module: HashMap<Symbol, ModuleFullPath>,
    pub intrinsics: IntrinsicTable,
    pub type_defs: HashMap<TypeName, TypeDefInfo>,
    pub constructor_to_type: HashMap<Symbol, TypeName>,
    pub expr_types: HashMap<Span, Type>,
    pub next_got_slot: usize,
}
```

The `IntrinsicTable` replaces the sketch's separate `primitive_entries`, `global_names`, `builtin_method_info`, and `trait_method_names` collections. It is a single structure enumerating all symbols that must be declared as imports in the ObjectModule:

```rust
/// All extern symbols that compiled code may reference.
/// Single source of truth -- shared between JIT setup and ObjectModule compilation.
pub struct IntrinsicTable {
    pub runtime_fns: Vec<IntrinsicEntry>,    // alloc, free, panic, trace_*, rc_*
    pub primitive_fns: Vec<IntrinsicEntry>,   // add-i64, str-concat, etc.
    pub platform_fns: Vec<IntrinsicEntry>,    // platform DLL functions
    pub global_names: HashSet<Symbol>,        // special forms + primitives (for liveness)
}

pub struct IntrinsicEntry {
    pub user_name: Symbol,
    pub jit_name: JitSymbol,
    pub param_count: usize,
}
```

This addresses the sketch's HIGH-1 (intrinsic coverage) and HIGH-3 (parameter explosion) simultaneously.

## 8. Pipeline Integration Points

### Design principle: cache-load/fresh-compile equivalence

**Steps [5-7] (cache load) MUST produce identical runtime state to steps [2-4] (fresh compilation).** This is the single most important invariant in the cache system. Specifically:

- The deserialized `SymbolTable` must have the same entries as a freshly typechecked module.
- The linked `.o` code must be callable at the same GOT slots as JIT-compiled code.
- Import resolution, macro registration, trait impl registration must all be replayed.

This invariant is not merely a correctness check — it is the architectural lever that enables path unification (see below). If cache-load and fresh-compile converge to the same state via the same code, bugs cannot hide in one path but not the other.

### Path unification strategy

The sketch's REPL and batch paths diverged incrementally as features were added. The reimplementation must actively minimise this divergence. Code volume and duplication between the two paths is a primary design metric.

#### Current divergence

The batch pipeline (`compile_module_graph`) accumulates all forms in a module, then typechecks and compiles them as a single `Program` via `check_program` + `compile_program`. The REPL (`ReplSession::eval`) typechecks and compiles per form via `check_repl_input` + `compile_and_execute`. Key shared code: `process_forms_sequentially()` (macro expansion), `build_program()` (AST construction). Key divergent code: typecheck entry point, codegen entry point, state management, error recovery.

#### Options for reducing divergence

**Option A: Per-form batch pipeline.** Batch module compilation feeds forms one at a time through the same per-form typecheck/compile path the REPL uses. Eliminates `compile_program` / `compile_module_program` entirely. Both modes use `check_repl_input` + per-form codegen.
- *Pro*: Maximum code sharing — one pipeline path for both modes. Cache equivalence trivially verifiable. Eliminates whole-program batch codegen path.
- *Con*: Loses cross-function batching within a module (compilation speed cost). May require adapting REPL-specific state management (snapshots, error recovery) to work in batch context.
- *Code impact*: Removes `compile_program` path (~200 lines), removes `check_program` batch path. Adds thin batch wrapper over REPL per-form loop.

**Option B: Shared compilation core with mode-specific entry points.** Extract the shared logic from both paths into a common `compile_module_forms()` function that both batch and REPL call. Batch accumulates and calls it once per module; REPL calls it per form. The shared core handles macro expansion, AST building, typecheck, and codegen.
- *Pro*: Retains batch compilation speed. Shared core reduces duplication without restructuring.
- *Con*: Two entry points remain — divergence can still accumulate. Cache equivalence requires testing both paths independently.
- *Code impact*: Refactors shared logic out of both paths. Both paths remain but with less duplication.

**Option C: Status quo with cache bolted on.** Keep current batch/REPL divergence, add caching as a layer around `compile_module_graph`.
- *Pro*: Least work for Sprint 22.
- *Con*: Cache equivalence is hard to verify with two compilation paths. Duplication continues to grow. The sketch took this approach and it led to the 15 audit findings.

**Recommendation**: Evaluate Options A and B during implementation. Option A is the simplest structurally (one path) but Option B may be necessary if per-form batch compilation reveals performance or correctness issues. Option C is rejected — it recreates the sketch's divergence problem. The evaluation should measure: lines of code in each path, number of branch points on CompileMode, and test surface (how many tests exercise both paths vs only one).

#### Cache-hit vs cache-miss

Regardless of which option above is chosen, the caching layer wraps the compilation path:

```
compile_or_load_module(module_id, manifest) -> ModuleState
```

This function handles both cache-hit and cache-miss for a single module:

```
Module graph discovered (topological order)
  |
  for each module in topo order:
    |
    [1. Check manifest] -- is this module cached with matching hash?
         |                    + are all dependencies' hashes current?
         |
         +-- cache miss --> [2. Per-form pipeline: read → expand → typecheck → codegen (per form)]
         |                        |
         |                   [3. Build CacheWritePacket]
         |                        |
         |                   [4. Submit to cache writer]
         |
         +-- cache hit  --> [5. Load .meta.json → reconstruct SymbolTable + ModuleStructure]
                            [6. Load .o → link into process (Linker) — see §13.3]
         |
         +-- (both) ------> [7. Install module scope (imports, macros, traits)]
```

Step [7] is shared — the same `install_module_scope()` function runs regardless of whether the module was freshly compiled or loaded from cache. This is where the equivalence invariant is enforced structurally: both paths feed the same installation function, so they cannot produce different installed state.

**Parameterization points (exhaustive list):**

Only three things differ between REPL and batch, and each is a small, well-bounded parameter:

| Parameterization | REPL | Batch | Why it cannot be eliminated |
|---|---|---|---|
| **Cache write scheduling** | Step [4] submits `CacheWritePacket` to a background mpsc thread. Non-blocking. | See options below. | The packet-building logic (`build_cache_packet()`) is shared; only the submission scheduling differs. |
| **Module discovery timing** | Modules loaded on first reference (lazy) | Full module graph discovered upfront (eager topo-sort) | REPL must respond to `(import ...)` typed interactively; batch knows the full dependency graph at startup. The per-module `compile_or_load_module` call is identical in both cases. |
| **Incremental monomorphisation** | New call sites may monomorphise already-cached constrained functions; specializations are JIT-compiled and added to GOT on demand | All specializations known before cache write | This is inherent to incremental vs whole-program compilation. Cached `.o` files contain the module's definitions at cache-write time; later specializations are cached with the module that triggered them. |

**Batch cache write scheduling options:**

The batch path needs to handle late monomorphisation — a downstream module may monomorphise a constrained function defined in an upstream module, adding specializations to the upstream's GOT. Three options:

- **Option W1: Deferred write.** Accumulate all packets; process in parallel after all modules compile (when all specializations are known). Simple, correct, but diverges from REPL's per-module write timing.
- **Option W2: Eager write with re-cache on mono.** Write each module's `.o` immediately after compilation (same as REPL). If a later module triggers monomorphisation of an already-cached module, re-compile and re-write that module's `.o`. Assumes late monomorphisation is rare. A heuristic stored in the cache metadata can record last-seen monomorphisations for a module, so the next compile pre-seeds them and avoids re-writes in the common case.
- **Option W3: Same as REPL.** Submit to the same background mpsc thread. Batch blocks on thread completion before linking. Maximises code sharing at the cost of not exploiting batch parallelism.

Option W2 is attractive because it unifies the write timing with the REPL path and the heuristic metadata makes re-writes rare in practice. Evaluate during implementation.

**What is NOT a parameterization point:**

- **GOT management**: both REPL and batch use GOT-indirect calls via `CompileMode::Interactive`. The reimplementation's `CompileMode` enum already shares the pipeline (`compile_unit()`); batch module compilation uses the same GOT-indirect calling convention so that cached `.o` files produced in either mode are interchangeable. `CompileMode::Release` (direct calls, no GOT, no caching) is reserved for full recompilation through an optimising backend (LLVM) where GOT indirection overhead is eliminated. Note: this was previously named `CompileMode::Batch` — renamed to `Release` to clarify its purpose.
- **Module scope installation**: `install_module_scope()` is the same code path for fresh compilation and cache load, in both REPL and batch.
- **Cache packet building**: `build_cache_packet()` is a pure function from `(SymbolTable, ModuleStructure, CacheCodegenState, compiled_functions)` to `CacheWritePacket`. Same function, both modes.
- **Cache loading**: `load_cached_module()` deserializes metadata and links the `.o`. Same function, both modes.
- **Manifest checking**: `check_manifest()` is a pure function. Same function, both modes.

## 9. Crate Ownership

| Component | Crate | Rationale |
|---|---|---|
| `CacheManifest`, `CachedModuleRef` | `cranelisp-backend` | Cache-specific types, no cross-crate need |
| `hash_source()` | `cranelisp-backend` | Pure function, used only by cache |
| `compile_module_to_object()` | `cranelisp-backend` | Cranelift dependency, ObjectModule API |
| `ObjectCompileInput`, `IntrinsicTable` | `cranelisp-backend` | Grouped parameters for object compilation |
| `CacheWritePacket` | `cranelisp-backend` | Send-safe snapshot, backend types |
| `build_cache_packet()`, `process_cache_packet()` | `cranelisp-backend` | Object compilation + file I/O |
| `Linker` | `cranelisp-backend` | Object file loading, relocation, mmap |
| `CacheWriter` (background thread) | `cranelisp` (binary) | Pipeline orchestration concern |
| Cache directory management | `cranelisp` (binary) | Project root discovery is CLI concern |
| Cache check in module graph loop | `cranelisp` (binary) | Pipeline orchestration |
| Module scope installation after load | `cranelisp` (binary) | Wires typecheck + backend state |
| `build_isa(is_pic: bool)` | `cranelisp-backend` | Single ISA construction point (architecture decision 7) |

### Why the Linker lives in backend, not binary

The Linker resolves relocations against JIT symbol addresses and manages executable memory regions. This is backend-internal knowledge (relocation formats, mmap semantics, GOT layout). The binary crate calls `linker.load_object(bytes)` and `linker.get_symbol(name)` but doesn't know about relocation types.

### Why CacheWriter lives in binary, not backend

The `CacheWriter` is a pipeline orchestration concern: it decides when to write caches, manages the thread lifecycle, and coordinates with the REPL session's shutdown. The backend provides `build_cache_packet()` and `process_cache_packet()` as pure functions; the binary crate decides when and how to call them.

## 10. Edge Cases

### REPL vs batch: remaining differences

Per the path unification strategy (§8), most REPL/batch differences have been eliminated. This table documents the residual differences and confirms that each is irreducible:

| Concern | Shared? | Detail |
|---|---|---|
| **Cache check** | Yes — same `check_manifest()` function | Timing differs (lazy vs eager discovery), but the per-module check is identical. |
| **Cache write** | Shared packet building; scheduling differs | `build_cache_packet()` is the same. REPL submits to background thread; batch accumulates then processes in parallel. This difference exists because batch must wait for monomorphisation to complete. |
| **GOT management** | Mode-dependent | Module compilation uses `CompileMode::Interactive` (GOT-indirect) in REPL and `CompileMode::Batch` (direct calls) in batch. Object files are not currently interchangeable between modes. `CompileMode::Release` is reserved for LLVM whole-program compilation where no caching occurs. |
| **Module scope installation** | Yes — same `install_module_scope()` | Both fresh-compile and cache-load feed the same function. |
| **Module reloading** | REPL only | Cache invalidated when source changes; dependent modules cascade-reloaded. Batch never reloads. This is inherent — batch runs once. |
| **Incremental monomorphisation** | REPL only | New REPL call sites may monomorphise already-cached constrained functions. Specializations are JIT-compiled and added to GOT on demand. The cached `.o` for the original module does not include these later specializations — they are cached with the module that triggered them, or regenerated on next load. Batch knows all specializations before cache write. |

### Cross-module dependencies

When module `A` is loaded from cache but its dependency `B` was recompiled (because `B` changed), `A` must be recompiled too. The transitive dependency check (section 3) handles this: `A`'s manifest entry includes `B`'s hash, and if `B`'s hash changed, `A` is invalidated.

**Import-only changes**: if `B` changes its private implementation but its public API (exported types, function signatures) is unchanged, `A`'s cache is still invalidated. This is conservative but correct. A future optimization could hash the public interface.

### Prelude caching

The prelude is a regular module and participates in caching like any other. Since every user module implicitly imports `(import [prelude [*]])`, a change to the prelude invalidates all user modules (via transitive dependency check). This is correct: prelude changes may alter available names, trait impls, or operator semantics.

All module caches (including stdlib) live in the project's `.cranelisp-cache/` directory. This avoids writing to potentially read-only locations (system-installed stdlib, fetched web dependencies). Only modules actually referenced by the project are compiled and cached — unused stdlib modules incur no cost.

**Cache directory layout** mirrors the module hierarchy:

```
project/
  .cranelisp-cache/
    manifest.json
    user.meta.json            # user module
    user.o
    core/
      core.meta.json          # core module (stdlib)
      core.o
      numerics.meta.json      # core.numerics module
      numerics.o
      option.meta.json        # core.option module
      option.o
    prelude.meta.json         # prelude module (stdlib)
    prelude.o
```

The directory structure directly mirrors the module hierarchy: `core.numerics` → `core/numerics.{meta.json,o}`. This is collision-free because module paths map 1:1 to filesystem paths. The entry module uses `_entry.meta.json`.

## 11. Three-Mode Compilation Support

Per spec C.5.3, the cache system participates in two of three modes:

### Dev mode (REPL JIT)

Cache is read on module load. JIT compiles for immediate execution. Background writer produces `.o` files for future quick-build use. This is the primary cache producer.

### Quick build mode

Reads cached `.o` files and links them via the system linker (`cc`) into a standalone executable. No Cranelift compilation occurs -- linking only. This mode requires that all modules have valid cached `.o` files. If any module is uncached, it must be compiled first (falling back to dev mode for that module).

The quick build pipeline:
1. Discover module graph.
2. For each module, verify cache is valid.
3. If all valid: collect `.o` files + runtime library, invoke system linker.
4. If any invalid: compile missing modules, write their `.o` files, then link.

This is the "quick build" goal: the common case (no source changes) is O(link time), not O(compile time).

### Release mode (`CompileMode::Release`)

Ignores the Cranelift cache entirely. Recompiles all reachable source through an optimising backend (LLVM) with direct calls (no GOT indirection). The `CheckResult + Program` boundary (architecture.md section "Single Pipeline Principle") ensures the LLVM backend receives the same input the Cranelift backend would. This is the only mode that uses `CompileMode::Release`.

## 12. Future Considerations

### Interface hashing (optimization)

The current transitive-dependency invalidation is source-hash-based: any change to a dependency invalidates importers. A more precise approach would hash a module's public interface (exported type signatures, trait impls, macro signatures) separately. If only the private implementation changes, importers' caches remain valid. This is a future optimization that doesn't affect the initial design.

### Two-phase compilation for parallel codegen

A potential future optimization: split compilation into two phases:
1. **Phase 1 (sequential)**: import scan, name resolution, and typechecking for all modules in topo order. This produces all GOT slot assignments and type information.
2. **Phase 2 (parallel)**: codegen for all modules simultaneously, since each module's codegen only needs the GOT layout and type info from Phase 1.

This would allow rayon parallelism across modules during codegen while keeping the sequential dependency resolution in Phase 1. Not needed for initial implementation (compilation speed is not the current priority) but the design should not preclude it.

### Parallel ObjectModule compilation

The sketch uses rayon `par_iter` for batch-mode cache writes. The reimplementation should do the same. Each `CacheWritePacket` is independent (no shared mutable state), making parallel `.o` compilation trivially safe.

### Static archive (.a) for quick build linking

For quick build mode, individual `.o` files could be bundled into a single `.a` (static archive) before invoking the system linker. Potential benefits:
- Fewer file arguments to `cc` — one `.a` instead of N `.o` files
- System linker may have optimised archive loading paths (single seek, symbol table index)
- Standard toolchain interop — `.a` files are well-understood by all linkers

Potential costs:
- Archive maintenance: must rebuild `.a` when any constituent `.o` changes (though `ar r` can update individual members)
- For the in-process linker (cache-hit loading in dev mode), individual `.o` files are loaded directly — the `.a` format adds unnecessary indirection

**Recommendation**: evaluate whether link time is a bottleneck in practice before adding `.a` generation. For the initial implementation, individual `.o` files are simpler. If quick build linking becomes slow with many modules, `.a` bundling is a localised optimisation to the quick build pipeline.

### Cache garbage collection

When modules are removed or renamed, their cache files become orphans. A periodic cleanup pass could compare the manifest's module list against the current module graph and remove stale entries. This is low priority -- orphaned files waste disk space but don't affect correctness.

## 13. ObjectModule Compilation and Loading — Concrete Implementation Design

**Status**: This section is the implementable specification for `.o` file generation and loading. It replaces the hand-waving in the earlier sections with concrete Cranelift API calls, data structures, and byte layouts. `/backend` implements against this section; `/int` wires the loading path.

### 13.1 What Goes in the `.o` File

The `.o` file is a standard relocatable object file produced by Cranelift's `cranelift-object` crate (`ObjectModule`). On macOS aarch64 it is Mach-O; on Linux aarch64 it is ELF. It contains:

1. **`__text` / `.text` section**: Machine code for every function defined in the module. Each function is an exported symbol (Linkage::Export) with the function's JIT name (e.g., `factorial`, `user/factorial`, `Display.show$Int`).

2. **`__data` / `.data` section**: The module's GOT table as a data symbol named `__cranelisp_got_<module_stem>` (e.g., `__cranelisp_got_user`, `__cranelisp_got_core_numerics`). This is an array of `next_got_slot * 8` bytes, with function-address relocations at each occupied slot. The GOT is `Linkage::Export` for the owning module and `Linkage::Import` for cross-module references.

3. **Relocations**:
   - Function-to-function calls within the module: `BRANCH26` / `CALL26` relocations.
   - GOT base loads: `GOT_LOAD_PAGE21` + `GOT_LOAD_PAGEOFF12` (Mach-O) or `ADR_PREL_PG_HI21` + `LDST64_ABS_LO12_NC` (ELF) pairs, referencing the GOT data symbol.
   - Cross-module GOT references: `Import` linkage data symbols for other modules' GOTs.
   - Intrinsic function calls: `Import` linkage function symbols for runtime functions (`runtime/alloc`, `runtime/dealloc`, `runtime/panic`, etc.) and primitive functions (`str-concat`, `int-to-string`, etc.).

The `.o` file does NOT contain:
- Type information (that is in `.meta.json`).
- Source text or AST (not needed for loading).
- Absolute addresses (everything is relocatable).

### 13.2 Generation Path — Cranelift API Calls

Generation happens in `process_cache_packet()` after `.meta.json` is written. The function `compile_module_to_object()` takes an `ObjectCompileInput` and returns `Vec<u8>`.

**Step-by-step with concrete API calls:**

```rust
pub fn compile_module_to_object(
    input: &ObjectCompileInput,
) -> Result<Vec<u8>, CranelispError> {
    // 1. Build PIC-mode ISA (already exists: build_isa(true))
    let isa = build_isa(true)?;

    // 2. Create ObjectModule
    let obj_builder = ObjectBuilder::new(
        isa,
        format!("cranelisp_{}", input.module_path),
        cranelift_module::default_libcall_names(),
    )?;
    let mut obj_module = ObjectModule::new(obj_builder);

    // 3. Declare per-module GOT data symbols
    //    - Own module's GOT: Linkage::Export, writable=true
    //    - Other modules' GOTs: Linkage::Import, writable=false
    let got_data_ids = declare_got_data_symbols(
        &mut obj_module,
        &input.module_path,
        &input.fn_to_module,
        &input.fn_slot_assignments,
    )?;

    // 4. Declare all intrinsic imports
    //    Each IntrinsicEntry becomes:
    //      let mut sig = obj_module.make_signature();
    //      sig.params = vec![AbiParam::new(types::I64); entry.param_count];
    //      sig.returns = vec![AbiParam::new(types::I64)];
    //      obj_module.declare_function(&entry.jit_name, Linkage::Import, &sig)?;
    let intrinsic_func_ids = declare_intrinsic_imports(
        &mut obj_module,
        &input.intrinsics,
    )?;

    // 5. Pass 1: Declare all module functions (get FuncIds)
    //    For each (defn, scheme) in input.defns:
    //      sig.params = [AbiParam::new(I64); defn.params.len()]
    //      sig.returns = [AbiParam::new(I64)]
    //      obj_module.declare_function(&defn.name, Linkage::Export, &sig)?;
    let declared_func_ids = declare_module_functions(
        &mut obj_module,
        &input.defns,
    )?;

    // 6. Define the GOT data section with function-address relocations
    //    let mut data_desc = DataDescription::new();
    //    data_desc.define(vec![0u8; next_got_slot * 8].into());
    //    data_desc.set_align(8);
    //    For each function in this module with a GOT slot:
    //      let func_ref = obj_module.declare_func_in_data(func_id, &mut data_desc);
    //      data_desc.write_function_addr((slot * 8) as u32, func_ref);
    //    obj_module.define_data(self_got_data_id, &data_desc)?;
    define_got_data(
        &mut obj_module,
        &input.module_path,
        &got_data_ids,
        &declared_func_ids,
        &input.defns,
        &input.fn_slot_assignments,
        &input.fn_to_module,
        input.next_got_slot,
    )?;

    // 7. Build ObjectModule-specific fn_slots with GotReference::DataSymbol
    //    For each (name, slot_info) in input.fn_slot_assignments:
    //      let data_id = look up module GOT via fn_to_module[name] -> got_data_ids[mod]
    //      FnSlot { got_ref: GotReference::DataSymbol(data_id), slot, param_count }
    let obj_fn_slots = build_obj_fn_slots(
        &input.fn_slot_assignments,
        &input.fn_to_module,
        &got_data_ids,
        &input.module_path,
    )?;

    // 8. Pass 2: Compile each function body
    //    For each (defn, scheme), using the SAME FnCompiler as JIT path:
    //      let mut func = Function::with_name_signature(...);
    //      FnCompiler::new(&mut func, &mut func_ctx, &mut obj_module, ...)
    //          .compile_body(defn, ...)?;
    //      let mut ctx = Context::for_function(func);
    //      obj_module.define_function(func_id, &mut ctx)?;
    compile_all_functions(
        &mut obj_module,
        &input,
        &declared_func_ids,
        &intrinsic_func_ids,
        &obj_fn_slots,
    )?;

    // 9. Emit the object file bytes
    let product = obj_module.finish();
    let bytes = product.emit()?;
    Ok(bytes)
}
```

**Critical detail — `GotReference` enum**: The `FnCompiler` must be parameterized over `Module` (both `JITModule` and `ObjectModule` implement `cranelift_module::Module`). In the JIT path, the GOT base is an `iconst` (absolute address). In the ObjectModule path, the GOT base is loaded via `module.declare_data_in_func(data_id, func)` which produces a `GlobalValue`, then `ins().global_value(I64, gv)` to load it. The `GotReference` enum mediates this:

```rust
/// How to obtain the GOT base pointer in generated code.
pub enum GotReference {
    /// JIT path: GOT base is a known absolute address, emitted as iconst.
    Immediate(i64),
    /// ObjectModule path: GOT base is a DataId, emitted as a global_value load.
    DataSymbol(cranelift_module::DataId),
}
```

In `FnCompiler`, the GOT load code becomes:

```rust
fn load_got_base(&mut self, got_ref: &GotReference) -> Value {
    match got_ref {
        GotReference::Immediate(addr) => {
            self.builder.ins().iconst(types::I64, *addr)
        }
        GotReference::DataSymbol(data_id) => {
            let gv = self.module.declare_data_in_func(*data_id, self.builder.func);
            let ptr = self.builder.ins().global_value(types::I64, gv);
            ptr
        }
    }
}
```

This is the **single point of divergence** between JIT and ObjectModule code paths. All other codegen is identical.

**FnCompiler generic over Module**: Currently `FnCompiler` takes `&mut JITModule`. It must become generic: `FnCompiler<'a, M: Module>`. This is a refactor of the `FnCompiler` struct and its methods. The `Module` trait from `cranelift_module` provides all needed methods: `declare_function`, `declare_data_in_func`, `make_signature`, etc. Both `JITModule` and `ObjectModule` implement it.

The alternative (avoiding generics) is to extract the `Module`-dependent operations behind a trait object or enum. The generic approach is cleaner because `Module` is already a trait with the right interface, and monomorphization eliminates virtual dispatch overhead.

### 13.3 Loading Path — From `.o` Bytes to Executable Code

On cache hit, the loading path is:

```
[1] Read .o bytes from disk
[2] Linker.load_object(module_name, &bytes)    // already implemented
[3] For each function defined in the .meta.json's codegen_state:
      [3a] addr = linker.get_symbol(fn_name)
      [3b] got_state.set_slot(slot, addr)        // wire into live GOT
      [3c] got_state.def_codegen[fn_name].code_ptr = Some(addr)
[4] Install module scope (shared with fresh-compile path)
```

**Step 2** is the existing `Linker::load_object()` in `crates/cranelisp-backend/src/cache/linker.rs`. It:
- Parses the `.o` via the `object` crate.
- Copies `__text` into an `mmap`'d region.
- Resolves relocations against registered symbols.
- Marks memory as executable via `mprotect`.
- Registers defined symbols in `linker.defined_symbols`.

Before calling `load_object`, the integration layer must register all external symbols the `.o` references:

```rust
// Register runtime intrinsics (from JIT builder symbols)
for (name, ptr) in &jit.builtin_symbols() {
    linker.register_symbol(name, *ptr);
}

// Register functions from already-loaded modules (topo order guarantees
// dependencies are loaded before dependents)
for (name, addr) in &already_loaded_fn_addrs {
    linker.register_symbol(name, *addr);
}

// Register GOT base pointers for already-compiled modules
// The .o file references __cranelisp_got_<mod> as an imported data symbol.
// The linker needs to know the address of each module's live GOT table.
for (mod_path, got_state) in &module_got_states {
    let got_symbol = format!("__cranelisp_got_{}", module_stem(mod_path));
    linker.register_symbol(&got_symbol, got_state.got_base_ptr());
}
```

**Step 3** wires loaded function pointers into the live GOT. The `CacheCodegenState` in `.meta.json` stores `got_slots: HashMap<Symbol, FnSlotInfo>` which maps function names to `(slot, param_count)`. After `load_object`:

```rust
for (fn_name, slot_info) in &cached_module.codegen_state().got_slots {
    if let Some(addr) = linker.get_symbol(fn_name.as_ref()) {
        got_state.set_slot(slot_info.slot, addr);
        // Also update def_codegen entry for REPL introspection
        if let Some(dc) = got_state.def_codegen.get_mut(fn_name) {
            dc.code_ptr = Some(addr);
        }
    }
}
```

**The GOT allocation question**: On cache hit, the `ModuleCodegenState` for the cached module must have a GOT table allocated with enough slots. The `CacheCodegenState.next_got_slot` field tells us the required size. The integration layer must:
1. Create a `ModuleCodegenState` (or reuse the session's).
2. Pre-allocate GOT slots up to `next_got_slot`.
3. The `got_base_ptr()` of this state is what gets registered with the linker as `__cranelisp_got_<mod>`.

For the REPL (single `ModuleCodegenState`), this means the existing GOT table is reused. For batch (per-module GOT), each cached module gets its own `ModuleCodegenState` restored from `CacheCodegenState`.

### 13.4 GOT Data Symbol Naming Convention

Each module's GOT is identified by a well-known data symbol name:

```
__cranelisp_got_<stem>
```

Where `<stem>` is the module's filesystem stem from `module_dir_and_stem()`:
- `user` -> `__cranelisp_got_user`
- `core.numerics` -> `__cranelisp_got_numerics`
- `prelude` -> `__cranelisp_got_prelude`
- Root entry -> `__cranelisp_got__entry`

This matches the sketch's convention. The symbol is `Export` in the owning module's `.o` and `Import` in any module that calls functions from it.

**IMPORTANT**: The stem alone is not unique across the module hierarchy (e.g., `core.option` and `app.option` both have stem `option`). Use the full module path with dots replaced by underscores: `__cranelisp_got_core_option`, `__cranelisp_got_app_option`. This is what `module_file_name()` in the sketch does (with the collision risk noted in LOW-4). The reimplementation's `module_dir_and_stem()` already handles this correctly via nested directories, but the GOT symbol name must use the flat form for linker compatibility. Define a helper:

```rust
fn got_data_symbol_name(module_path: &ModuleFullPath) -> String {
    let flat = module_path.as_ref().replace('.', "_");
    format!("__cranelisp_got_{}", if flat.is_empty() { "_entry" } else { &flat })
}
```

### 13.5 The `declare_got_data_symbols` Function

This declares data symbols for every module whose GOT is referenced by the module being compiled:

```rust
fn declare_got_data_symbols(
    obj_module: &mut ObjectModule,
    self_path: &ModuleFullPath,
    fn_to_module: &HashMap<Symbol, ModuleFullPath>,
    fn_slot_assignments: &HashMap<Symbol, FnSlotInfo>,
) -> Result<HashMap<ModuleFullPath, DataId>, CranelispError> {
    let mut got_data_ids: HashMap<ModuleFullPath, DataId> = HashMap::new();

    // Collect all referenced modules
    let mut referenced_modules: HashSet<ModuleFullPath> = HashSet::new();
    referenced_modules.insert(self_path.clone());
    for mod_path in fn_to_module.values() {
        referenced_modules.insert(mod_path.clone());
    }

    for mod_path in &referenced_modules {
        let symbol_name = got_data_symbol_name(mod_path);
        let is_self = mod_path == self_path;
        let data_id = obj_module.declare_data(
            &symbol_name,
            if is_self { Linkage::Export } else { Linkage::Import },
            is_self,  // writable: true for self (we define it), false for imports
            false,    // tls: false
        )?;
        got_data_ids.insert(mod_path.clone(), data_id);
    }

    Ok(got_data_ids)
}
```

### 13.6 Edge Cases

#### Modules with no codegen (type-only modules)

If a module defines only types, traits, and constructors (no `defn` forms), `ObjectCompileInput.defns` is empty. `compile_module_to_object()` should produce an empty `.o` (zero-length `__text`), or skip `.o` generation entirely. On cache hit, the `has_object: false` flag signals that only metadata restoration is needed. The `try_load_cached_module` already checks for this.

**Decision**: Skip `.o` generation when `defns` is empty. Set `has_object: false` in the cached metadata. On load, skip the linker step. This avoids writing and parsing trivial object files.

#### Modules with macros

Macros are expanded at compile time and do not produce machine code in the `.o` file. The macro's `MacroClauseInfo` (parameter patterns, compiled function pointers) is stored in `.meta.json` under `SymbolTable` entries of kind `Macro`. On cache hit, the macro must be re-compiled from source to get fresh function pointers — macro expansion requires executable code (the macro body), which is JIT-specific and cannot be cached in a relocatable `.o`.

**Decision**: On cache hit for a module containing macros:
1. Restore the `SymbolTable` from `.meta.json` (gives type info, visibility, macro clause metadata).
2. Load the `.o` for regular functions.
3. Re-compile macro bodies via the JIT path (parse the `defmacro` forms from the cached `ModuleStructure.impl_sexps` or re-read source). This is fast — macros are typically small.

This is the same approach the sketch uses. The alternative (caching compiled macro code in the `.o`) would require the macro expansion runtime to call through the linker, adding complexity for minimal gain.

#### Cross-module function references

When module `A` calls a function defined in module `B`, the generated code in `A`'s `.o` loads `B`'s GOT base via an imported data symbol (`__cranelisp_got_B`), then indexes into it. The linker resolves this import to the live address of `B`'s GOT table.

**Topo-order loading guarantee**: Modules are loaded in topological order (dependencies before dependents). When loading `A`'s `.o`, module `B` is already loaded and its GOT base address is known. The integration layer registers `B`'s GOT address with the linker before loading `A`.

**Cross-module function pointers in the GOT**: Module `B`'s GOT contains function pointers for `B`'s functions. These are populated either by the JIT (fresh compile) or by the linker (cache load). Either way, by the time `A`'s code runs, `B`'s GOT has valid pointers.

#### Constrained polymorphic functions and monomorphisation

Constrained polymorphic functions (e.g., `(defn add [x y] (+ x y))`) are monomorphised at call sites. The specializations (e.g., `add$Int+Int`) are compiled and cached with the module that triggered the monomorphisation. The original constrained function's `defn` is stored in `.meta.json` for future monomorphisation needs.

On cache hit, if a new call site requires a specialization not in the cached `.o`, the pipeline falls back to JIT compilation for that specialization only. This is the same as the REPL's on-demand monomorphisation path.

#### The `__data` vs `__bss` GOTCHA (from sketch)

The GOT data section MUST use `data_desc.define(vec![0u8; size].into())` (explicit zero bytes), NOT `data_desc.define_zeroinit(size)`. The latter places data in `__bss` (BSS) on Mach-O, which has no file-backed content. The system linker crashes (SIGSEGV) when applying relocations to BSS on macOS. This was a hard-won discovery in the sketch. The explicit zero bytes place the GOT in `__DATA,__data`, which has file-backed content and supports relocations.

### 13.7 Required Code Changes

This section lists the concrete changes each skill must make.

#### `/backend` changes

1. **Add `GotReference` enum** to `crates/cranelisp-backend/src/compiler/mod.rs` (or a new `got_ref.rs`):
   ```rust
   pub enum GotReference {
       Immediate(i64),
       DataSymbol(cranelift_module::DataId),
   }
   ```

2. **Make `FnCompiler` generic over `M: Module`**. Currently it holds `&'a mut JITModule`. Change to `&'a mut M` where `M: Module`. All methods that call `self.module.declare_function()` etc. work unchanged because both `JITModule` and `ObjectModule` implement `Module`.

   Affected files:
   - `crates/cranelisp-backend/src/compiler/mod.rs` — struct definition, `new()`, `compile_body()`
   - `crates/cranelisp-backend/src/compiler/apply.rs` — `resolve_got_entry()` must use `GotReference`
   - `crates/cranelisp-backend/src/compiler/control_flow.rs` — auto-curry GOT loads
   - `crates/cranelisp-backend/src/compiler/trace_codegen.rs` — trace wrapper compilation
   - `crates/cranelisp-backend/src/compiler/vec_codegen.rs` — if it calls module methods
   - `crates/cranelisp-backend/src/compiler/match_codegen.rs` — if it calls module methods
   - `crates/cranelisp-backend/src/jit.rs` — `compile_defn()` now creates `FnCompiler<JITModule>`

3. **Implement `compile_module_to_object()`** in `crates/cranelisp-backend/src/cache/object.rs`, following the structure in section 13.2. This replaces the current stub comment.

4. **Wire `compile_module_to_object()` into `process_cache_packet()`**:
   ```rust
   pub fn process_cache_packet(packet: &CacheWritePacket) -> Result<ProcessedPacket, CranelispError> {
       // Write .meta.json (existing)
       super::atomic_write(&packet.meta_path, &packet.meta_json_bytes)?;

       // Compile and write .o (NEW)
       if !packet.object_compile_input.defns.is_empty() {
           let obj_bytes = compile_module_to_object(&packet.object_compile_input)?;
           super::atomic_write(&packet.object_path, &obj_bytes)?;
       }

       Ok(ProcessedPacket { ... })
   }
   ```

5. **Populate `CacheCodegenState.got_slots`** in the cache packet builder. Currently `got_slots` is always empty. The integration layer must fill it from `ModuleCodegenState.def_codegen` when building the packet.

6. **Add `got_data_symbol_name()` helper** to `crates/cranelisp-backend/src/cache/mod.rs`.

7. **Add `object` crate dependency** to `crates/cranelisp-backend/Cargo.toml` (already present for the linker; verify `cranelift-object` is also present for `ObjectModule`/`ObjectBuilder`).

#### `/int` changes

1. **On cache hit with `.o`**: After `try_load_cached_module()` returns `CachedModule { has_object: true, .. }`:
   ```rust
   // Read .o bytes
   let obj_bytes = std::fs::read(&cached.object_path)?;

   // Register external symbols with linker
   register_linker_externals(&mut linker, &jit, &module_got_states);

   // Load the .o
   linker.load_object(&module_path.to_string(), &obj_bytes)?;

   // Wire function pointers into live GOT
   for (fn_name, slot_info) in &cached.codegen_state().got_slots {
       if let Some(addr) = linker.get_symbol(fn_name.as_ref()) {
           got_state.set_slot(slot_info.slot, addr);
           // Ensure def_codegen entry exists with code_ptr
       }
   }
   ```

2. **Linker lifetime**: The `Linker` must live as long as the `CompilationSession` (its `code_regions` hold the executable memory). Add `linker: Option<Linker>` to `CompilationSession`.

3. **GOT state restoration**: When a cached module is loaded, its `CacheCodegenState.next_got_slot` must be used to advance the session's GOT slot counter so fresh compilations don't collide with cached slots.

4. **Populate `ObjectCompileInput` fully** when building cache packets. Currently the integration layer creates `ObjectCompileInput` with mostly empty fields. Wire in:
   - `defns`: from the compiled `Program`'s defns + their inferred schemes
   - `fn_slot_assignments`: from `got_state.def_codegen`
   - `fn_to_module`: from the module graph's symbol ownership
   - `intrinsics`: from JIT's builtin symbol registry
   - `type_defs`, `constructor_to_type`, `expr_types`: from `CheckResult`
   - `method_resolutions`: from `CheckResult`
   - `next_got_slot`: from `got_state`

### 13.8 Implementation Order

The changes above have dependencies. Recommended implementation order:

1. **Phase 1 — `GotReference` + generic `FnCompiler`** (`/backend`): Add the enum, make `FnCompiler<M: Module>`, verify all existing tests pass. This is the largest refactor and must happen first. No `.o` files yet — just structural preparation.

2. **Phase 2 — `compile_module_to_object()`** (`/backend`): Implement the function using `FnCompiler<ObjectModule>`. Write unit tests that compile a simple module to `.o` and verify the bytes are parseable via the `object` crate.

3. **Phase 3 — Wire into `process_cache_packet()`** (`/backend`): Enable `.o` generation in the background writer. Populate `ObjectCompileInput` fields from the integration layer (`/int`).

4. **Phase 4 — Loading path** (`/int` + `/backend`): Add `Linker` to `CompilationSession`. On cache hit with `has_object: true`, load the `.o`, wire into GOT, skip JIT compilation. Integration tests: compile a module, verify cache produces `.o`, clear JIT, load from cache, verify functions execute correctly.

5. **Phase 5 — End-to-end tests** (`/qa`): Multi-module projects with cache, reload after source change, constrained polymorphism across cache boundaries.

### 13.9 Sketch Comparison for This Section

The sketch's `compile_module_to_object()` (cache.rs lines 362-647) follows the same dual-compilation pattern described here. Key differences in the reimplementation:

| Aspect | Sketch | Reimplementation |
|--------|--------|------------------|
| Function entry point | 21 positional parameters | `ObjectCompileInput` struct |
| ISA construction | Inline `settings::builder()` | `build_isa(true)` shared helper |
| Intrinsic declaration | Per-intrinsic params (alloc_jit_name, etc.) | `IntrinsicTable` loop |
| `FnCompiler` | `compile_function_indirect` takes `&mut impl Module` | `FnCompiler<M: Module>` generic struct |
| GOT reference | `GotReference` enum on `FnSlot` | Same pattern, cleaner placement |
| Global names for liveness | `build_minimal_modules_for_codegen` hack | `IntrinsicTable.global_names` (no fake module) |

The linker (`linker.rs`) is already ported nearly verbatim. The reimplementation's linker adds `Result` returns instead of panics, and a capacity field for future growable GOT.

The sketch's approach to macro re-compilation on cache hit, cross-module GOT references via data symbols, and the `__data` vs `__bss` workaround are all adopted without divergence — they are correct solutions to real problems.

### 13.10 Risks and Mitigations

| Risk | Likelihood | Impact | Mitigation |
|------|-----------|--------|------------|
| `FnCompiler<M: Module>` refactor breaks existing tests | Medium | High | Phase 1 is purely structural — all tests must pass before proceeding. |
| `ObjectModule` generates different code than `JITModule` for same input | Low | High | Both use the same `FnCompiler` code. Only GOT load differs. Verify with disassembly comparison. |
| Relocation types not handled by linker | Low | Medium | Linker already handles all Cranelift-emitted relocation types (tested in sketch). Add panic-on-unknown for early detection. |
| ADRP range exceeded (code and GOT >4GB apart) | Very Low | Medium | `mmap` allocations are typically in the same region. If hit, allocate code near GOT via `MAP_FIXED` hint. |
| Macro re-compilation from source is slow | Very Low | Low | Macros are small. If measured as a bottleneck, cache macro code in the `.o` (future optimization). |

### 13.11 Implementation Defect: Parallel Compilation Paths (Sprint 53)

**Status**: MUST FIX — object path crashes on multi-sig defns; root cause is duplicated compilation logic.

#### The Problem

The JIT (in-memory) and object (.o file) compilation paths are separate implementations that should be the same code parameterised by the Cranelift module type. Instead:

- **JIT path** (`compile_program` in `lib.rs`): takes `(program, check, symbol_tables)`, internally collects defns, expands multi-sig, declares functions against `JITModule`, compiles bodies.
- **Object path** (`compile_module_to_object` in `cache/object.rs`): takes `ObjectCompileInput`, a separate struct assembled by `build_object_compile_input` in `pipeline.rs`, which re-derives defn lists and slot assignments from the AST.

This duplication causes:
1. **Multi-sig crash**: `collect_defns_for_cache` calls `defn.params()` on DefnMulti — panics. The JIT path handles multi-sig correctly; the object path doesn't because it's separate code.
2. **Invented slot numbers**: `collect_defns_for_cache` assigns sequential slots (0, 1, 2, ...) instead of reading the real GOT slots from the symbol table.
3. **Redundant data assembly**: `ObjectCompileInput` carries `fn_slot_assignments`, `fn_to_module`, `cross_module_fns`, `next_got_slot` — all derivable from the symbol table. `CodegenInput` carries `cross_module_func_sigs` for the same reason.

#### Analysis: What Both Paths Need

Both JIT and object compilation need exactly three inputs:

1. **`program`** — AST bodies (the source to compile)
2. **`CheckResult`** — typecheck products: method_resolutions, expr_types, constrained_fn_names, mono_defns, default_method_defns
3. **`symbol_tables`** — GOT slots, import chains, schemes, cross-module refs

Everything else (`fn_slot_assignments`, `fn_to_module`, `intrinsics`, `next_got_slot`, `cross_module_fns`) is either on the symbol table already or is a static table (intrinsics). `ObjectCompileInput` exists because the object path was built separately instead of sharing the JIT path's logic.

The only genuine difference between the two outputs is how GOT references are encoded:
- **JIT**: `GotReference::RuntimePtr(i64)` — direct pointer to GOT table in memory
- **Object**: `GotReference::DataSymbol(DataId)` — relocatable reference resolved by linker

#### Correct Design

One compilation function parameterised by module type:

```rust
pub fn compile_to_module<M: Module>(
    program: &Program,
    check: &CheckResult,
    symbol_tables: &DashMap<ModuleFullPath, SymbolTable>,
    module: &mut M,
) -> Result<CompiledProgram, CranelispError>
```

The caller (priority worker or nice worker) creates the appropriate module:

```rust
// Priority worker (JIT / in-memory):
let mut jit_module = JITModule::new(jit_builder);
let result = compile_to_module(program, check, symbol_tables, &mut jit_module)?;

// Nice worker (object / .o file):
let mut obj_module = ObjectModule::new(obj_builder);
let result = compile_to_module(program, check, symbol_tables, &mut obj_module)?;
let bytes = obj_module.finish().emit()?;
```

The GOT reference strategy is handled inside `compile_to_module` via the `Module` trait — `declare_data`, `declare_func_in_data`, etc. have the same API on both `JITModule` and `ObjectModule`.

#### What To Delete

- `ObjectCompileInput` struct (cache/object.rs)
- `collect_defns_for_cache` (pipeline.rs)
- `build_object_compile_input` (pipeline.rs)
- `cross_module_func_sigs` field on `CodegenInput` (session_v4.rs)
- `compile_module_to_object` wrapper that takes `ObjectCompileInput` — replaced by `compile_to_module<ObjectModule>`

#### What To Keep

- `CodegenInput` retains its legitimate fields: `program`, `method_resolutions`, `expr_types`, `mono_defns`, `default_method_defns` — these are typecheck products not on the symbol table.
- `CodegenInput` effectively becomes the stashed `CheckResult` + `program`. Consider whether it should just BE `(CheckResult, Program)`.
- `IntrinsicTable` — but built once and shared, not assembled per-module.

#### `--link` Mode

The `--link` path compiles to .o without doing JIT. This works naturally: the worker creates an `ObjectModule` and calls `compile_to_module`. There is no `InmemCompileInput` vs `ObjectCompileInput` distinction — both modes call the same function with different module types.

#### Fix Approach

1. Unify `compile_program` and `compile_module_to_object` into `compile_to_module<M: Module>`.
2. All structural data (GOT slots, imports, cross-module refs) read from `symbol_tables` inside the function.
3. Delete the redundant types and assembly functions listed above.
4. Nice worker stashes `(CheckResult, Program)` instead of `CodegenInput` — or `CodegenInput` is simplified to just those fields.
5. Priority and nice workers both call `compile_to_module` with their respective module type.

## 14. Step 5b — Cache rewrite via `SymbolTable` serialisation (Sprint 58, Phase 5)

**Status**: PRESCRIPTIVE for Sprint 58 Wave 2. Supersedes §4 ("Serialization Format") for the persisted shape; supersedes §13.x parts that named `CacheCodegenState` / `CacheMetadata` as separate top-level decomposed types. §4 and §13 remain on the page as historical context — §14 is authoritative for the Phase-5 cache.

**Decisions consumed**: Decision 25 (`code` on `ModuleEntry::Def.code`, `#[serde(skip)]`), Decision 26 (platform fn ptrs likewise), Decision 31 (`Arc<Jit>` lifetime; per-batch reclaim), Decision 32 (`CodeStore`/`LinkerStore` empty marker traits), Decision 33 (structural decls live as `SymbolTable` fields; `ModuleStructure` dissolves), Decision 34 (`schema_version: u32` envelope; mismatch invalidates as cache-stale).

### 14.1 Persisted shape

The `.meta.json` file is a serialised `SymbolTable<(), ()>` — the typecheck-product shape. Concretely, it contains:

| Field | Source (Step 5a) | On-disk presence |
|---|---|---|
| `path: ModuleFullPath` | identity | yes |
| `symbols: HashMap<Symbol, ModuleEntry<()>>` | populated incrementally during typecheck | yes — each entry's serde-visible fields (Def: `scheme`, `visibility`, `docstring`, `param_names`, `kind`, `callees`, `got_slot`, `trait_origin`, `ast`; Import: `source`; etc.) |
| `next_got_slot: usize` | allocated during registration | yes |
| `got: Arc<GotTable>` | runtime memory | `#[serde(skip, default = "default_got_arc")]` — re-derived at load |
| `imports: Vec<ImportSpec>` | written by worker form-handlers (Step 5a) | yes |
| `exports: Vec<ExportSpec>` | (same) | yes |
| `platforms: Vec<PlatformSpec>` | (same) | yes |
| `submodules: Vec<ModDecl>` | (same) | yes |
| `schema_version: u32` | written by cache-write path; defaults to 0 on legacy caches | yes (`#[serde(default)]`) |
| `linker: Option<L>` | runtime; cache-restore re-derives via mmap | `#[serde(skip)]` — `L = ()` for the cached shape |

For each `ModuleEntry::Def` inside `symbols`:
- `code: Option<C>` — `#[serde(skip)]`. Not in the file. Re-derived by re-running codegen against `ast`.
- `platform_fn_ptr: Option<*const u8>` — `#[serde(skip)]`. Not in the file. Re-derived by re-resolving the platform DLL named by the persisted `PlatformDecl` and reading its manifest (Decision 26).

The `.o` file (per-module `ObjectModule` output) remains the second on-disk artefact. Its content is unchanged from §13.1; what changes is how the loader rebuilds in-memory state around it.

The previous separate `CacheMetadata` struct (in `crates/cranelisp-backend/src/cache/serialize.rs`) becomes a thin envelope OR dissolves entirely, depending on whether the round-trip needs out-of-band data:

```rust
/// Either: a thin wrapper that adds version metadata that doesn't fit cleanly
/// on SymbolTable (e.g. compiler binary mtime, target triple). If SymbolTable's
/// schema_version + manifest.json's per-binary fields suffice, the envelope
/// dissolves entirely.
#[derive(Serialize, Deserialize)]
pub struct CacheEnvelope {
    pub schema_version: u32,
    pub table: SymbolTable<(), ()>,
}
```

Decision 34's text permits either approach. The recommendation: if `serde`'s default behaviour can derive `schema_version` from `SymbolTable` directly (it can — the field exists on the struct per §14.1's table), no envelope is needed and the `.meta.json` IS the serialised `SymbolTable`. If serde's forward-compatibility on field additions/deletions surfaces a reason to externalise the version (e.g. handling a future enum-variant rename), introduce `CacheEnvelope` then. Sprint 58 ships without the envelope and revisits if needed.

### 14.2 `CACHE_SCHEMA_VERSION` ownership

Per Decision 34 + `/arch` Sprint 58 review condition 2: `/backend` owns the `CACHE_SCHEMA_VERSION` constant. Canonical location:

```rust
// crates/cranelisp-backend/src/cache/mod.rs
//
// Bump this whenever the persisted shape of SymbolTable changes in a way
// serde cannot tolerate via #[serde(default)] on additive fields:
//   - Field deletions: bump.
//   - Field type changes (T → U where deserialise<U> would fail on persisted T): bump.
//   - Enum variant additions to a serde-tagged enum used inside SymbolTable: bump (forward-compat depends on the enum's #[serde(...)] attributes).
//   - Field additions with #[serde(default)] AND the default matches a fresh-build value: NO bump needed.
//   - Variant renames: bump.
pub const CACHE_SCHEMA_VERSION: u32 = 1;
```

Sprint 58 Wave 2 ships `CACHE_SCHEMA_VERSION = 1` (the first numbered shape; pre-Sprint-58 caches lack the field and deserialise as `0`, which mismatches `1` and invalidates as cache-stale). The pre-existing `CACHE_FORMAT_VERSION` constant on `cache/mod.rs:30` is renamed to `CACHE_SCHEMA_VERSION` in this rewrite — the semantic is the same, and the new name matches Decision 34's wording so `/int`'s `symbol-table-cache.md` and the architecture decision use one term.

`/int`'s worker cache-write path (in `src/worker.rs`) emits the field by reading `CACHE_SCHEMA_VERSION` and writing it onto the `SymbolTable.schema_version` field before serialisation. Cross-reference: `design/int/symbol-table-cache.md` is the producer-side companion to this section; the two docs MUST agree on the constant's name and its location.

### 14.3 Cache-restore (load path)

On cache-hit, the loading path becomes:

```text
[1] Read .meta.json bytes from disk.
[2] Deserialise via `serde_json::from_slice::<SymbolTable<(), ()>>(bytes)`.
[3] Check `table.schema_version == CACHE_SCHEMA_VERSION`. Mismatch → return
    `CacheStale::SchemaMismatch { found, expected }`; caller treats as
    invalidated (same code path as source-mtime change).
[4] Insert the deserialised SymbolTable into the session's
    `tc.symbol_tables: DashMap<ModuleFullPath, SymbolTable<C, L>>` —
    promoting `()` to `C, L` happens at the DashMap insertion site in
    `src/session_v4.rs` (the integration layer; see Step 5c).
[5] Re-derive runtime state per ModuleEntry::Def in topological order:
    [5a] If `entry.platform_fn_ptr_target` (i.e. `kind == Primitive { primitive_kind:
         PlatformEffect, .. }`): re-open the platform DLL named by the persisted
         `PlatformDecl` (look it up via `symbol_table.platforms`), read its manifest,
         locate the matching cl_name → fn_ptr, and write into `entry.platform_fn_ptr`.
         If the DLL is missing or the manifest no longer exports the name →
         `CacheStale::PlatformResolutionFailed { module, symbol }`.
    [5b] If the entry has `ast: Some(_)`: re-run codegen via `compile_to_module<JITModule>`
         (priority worker) for that single symbol — exactly the same call path as
         fresh-build. The freshly-allocated `Arc<Jit>` lives on `entry.code` per
         Decision 25 + Decision 31 Scenario 2. Do NOT load the .o file for this
         entry (the .o is the nice-worker product; cache-restore for JIT goes
         through codegen for parity with fresh build).
    [5c] If the entry has `ast: None`: nothing to re-derive — it's a primitive,
         a special form, an Overloaded base (variants carry the bodies), a
         constrained-fn template (mono specialisations carry the bodies), an
         Import, a Reexport, a TypeDef, a TraitDecl, a Constructor, a Macro,
         or an Ambiguous. Each of those categories' runtime needs are handled
         by their own kind-specific code paths (none require .o loading).
[6] If --link mode (cache-hit on .o for batch nice-worker output): load the
    .o via `Linker::load_object` and write the resolved fn ptrs into the
    session's GOT directly, bypassing JIT codegen. Set the SymbolTable's
    `linker` field to the freshly-mmap'd Linker handle. (This is the
    quick-build path of §11.)
[7] Install module scope (imports, macros, traits) — shared with fresh-build
    via `install_module_scope()`. The deserialised SymbolTable's
    structural-decl fields (`imports`/`exports`/`platforms`/`submodules`)
    are the input to the import resolver, so cache-restore and fresh build
    feed the same resolver.
```

Step [5b] is the load-bearing simplification: cache-restore for JIT mode does NOT load the .o file. Instead, it re-runs codegen against the deserialised `ast` body. The .o file exists only for `--link` mode (step [6]). The rationale: keeping cache-restore equivalent to fresh-build by going through `compile_to_module` means there is exactly one codegen path, exactly one `Arc<Jit>` lifetime story (Decision 31 Scenario 2 fires consistently), and no separate "load .o into mmap" code path for the dev REPL workflow. The .o file is produced eagerly by the nice worker for `--link` reuse, but the dev workflow does not pay the .o-load cost.

Trade-off: cache-restore in JIT mode pays codegen cost on every restart. Sketch-comparison evidence is that JIT codegen for a single symbol is sub-millisecond (the priority worker already hits this latency for REPL evals). The cache hit eliminates typecheck cost (the dominant cost for non-trivial modules) and the structural-decl/symbol/scheme rebuild — what's left is pure CLIF emission against pre-typed AST. If profiling reveals codegen cost dominates, a future optimisation can add a per-symbol `.code.bin` artefact to the cache directory; the symbol-table shape does not need to change.

### 14.4 `CodegenInput` stashing path is deleted

Pre-Phase-5 worker code (Sprint 56–57) stashed a `CodegenInput { program, method_resolutions, expr_types, mono_defns, default_method_defns }` value at typecheck-completion time so the priority worker could replay codegen later. Step 5b deletes this stashing path entirely. The replacement: `compile_to_module` reads everything it needs from the symbol table (annotations are on AST nodes per Sprint 55; mono/default bodies are on mangled `ModuleEntry::Def` entries per Sprint 56 Phase 2). The worker handing a single name to `compile_to_module` is the same on cache-hit (after re-deserialisation) and fresh-build.

Concretely deleted from `crates/cranelisp-backend/src/cache/`:

- `serialize::CacheMetadata` — replaced by the `schema_version` field on `SymbolTable` (or a thin `CacheEnvelope` per §14.1 if serde forward-compat needs it).
- `serialize::CacheCodegenState` — every field migrates onto the `SymbolTable.symbols` entries. `got_slots` becomes `ModuleEntry::Def.got_slot`. The "param counts for fast lookup" disappear (codegen reads from the AST). `def_codegen` (REPL introspection metadata) was already migrated to the symbol-table entry's introspection fields in earlier sprints.
- The `CodegenInput` stashing struct (in `src/worker.rs` or `src/session_v4.rs` — owned by `/int`) — its consumers all pull from the symbol table now.
- `try_load_cached_module()`'s 238-line import-resolution duplication (MED-2) — the cache-restore path of §14.3 step [7] reuses `install_module_scope()` directly.

### 14.5 Cache-write path

Symmetric to load:

```text
[1] Worker completes typecheck for a module.
[2] Worker (or background writer thread) takes a snapshot of the symbol
    table for that module — typically a `clone` of the `SymbolTable` from
    the DashMap. The clone is `SymbolTable<C, L>` but every `code` /
    `platform_fn_ptr` / `got` / `linker` field is `#[serde(skip)]`, so the
    serialiser's view is `SymbolTable<(), ()>`-equivalent.
[3] Set `cloned.schema_version = CACHE_SCHEMA_VERSION`.
[4] `serde_json::to_vec(&cloned)` → `meta_json_bytes`.
[5] Atomic write to `<cache_dir>/<module_path>.meta.json` (temp-file-then-rename).
[6] If batch / --link / nice-worker: separately invoke `compile_to_module<ObjectModule>`
    on `defined_symbols(symbol_table)` to produce `.o` bytes, atomic-write
    to `<cache_dir>/<module_path>.o`.
[7] Update manifest.json (per §3) with the module's source hash and dep
    hashes.
```

The cache-write path is single-source-of-truth: the symbol table IS the input. There is no parallel "build a packet from scattered session state" step (the sketch's `CacheWritePacket` and the Sprint-22 `ObjectCompileInput` both decompose). For the `.o` write, `compile_to_module` reads the `defined_symbols` iterator off the symbol table itself. Cross-reference: `/int`'s `symbol-table-cache.md` documents the worker-side write trigger and any background-thread coordination.

### 14.6 Symmetry invariant (mirrors §8 design principle)

The §8 invariant — "cache-load and fresh-compile MUST produce identical runtime state" — sharpens under §14:

> Fresh-build path: typecheck populates `SymbolTable`; `compile_to_module` populates `code` per Defn entry; `install_module_scope` registers imports/macros/traits.
>
> Cache-restore path: deserialise populates `SymbolTable`; `compile_to_module` populates `code` per Defn entry (driven by the deserialised `ast`); `install_module_scope` registers imports/macros/traits.

The two paths converge into the same symbol-table shape via the same code (`compile_to_module` + `install_module_scope`). Anything that's true after fresh-build is true after cache-restore by construction — there's no separate "rehydrator" function whose behaviour can drift.

Test this invariant via round-trip: `serde_json::from_slice::<SymbolTable<(),()>>(serde_json::to_vec(&fresh_table).unwrap())` must equal the original on every field that is not `#[serde(skip)]`. `/backend` writes the unit tests; `/qa` writes the integration tests (cache hit reproduces correct execution).

### 14.7 Failure modes (CacheStale discriminator)

```rust
pub enum CacheStale {
    /// Source file's content hash changed.
    SourceChanged { module: ModuleFullPath, old_hash: String, new_hash: String },
    /// Transitive dependency hash changed.
    DependencyChanged { module: ModuleFullPath, dep: ModuleFullPath },
    /// schema_version on disk doesn't match CACHE_SCHEMA_VERSION (Decision 34).
    SchemaMismatch { module: ModuleFullPath, found: u32, expected: u32 },
    /// Compiler binary mtime changed.
    CompilerChanged,
    /// Target triple or Cranelift version changed (manifest-level).
    EnvironmentChanged { what: &'static str },
    /// Platform DLL no longer resolves the manifest entry the cached entry expects.
    PlatformResolutionFailed { module: ModuleFullPath, symbol: Symbol },
}
```

Every variant maps to the same caller-visible behaviour: invalidate, recompile from source, write a fresh cache entry. The discriminator exists for diagnostics and tests, not for branching control flow.

### 14.8 Sketch comparison refresh (Phase 5)

This subsection refreshes §2 ("Sketch Comparison") for the Phase-5 persisted shape, satisfying `/arch` Sprint 58 review condition 1.

**Sketch's cache shape**: the sketch persisted the monolithic `CompiledModule` struct as JSON. `CompiledModule` was the in-memory god-object holding symbols, GOT slots, runtime function pointers, codegen state, import scopes, macro tables, and trait registries — all in one struct. Cache writes serialised it via `serde` with `#[serde(skip)]` on the runtime-pointer fields; cache reads deserialised it and ran a 238-line "rehydrator" (`try_load_cached_module()`) that re-installed scopes/macros/traits from the deserialised state. The sketch did not separate "structural specification" (the original `(import …)` / `(export …)` / `(platform …)` / `(mod …)` forms in source order) from "resolved effects" (per-symbol entries created during typecheck). The CompiledModule held the resolved effects and the `(import …)` form list as one bag; regenerating source (for `(read-source <module>)` introspection) meant walking the entries and reconstructing the originals heuristically.

**v4-target cache shape (this section)**: the `.meta.json` IS a serialised `SymbolTable<(), ()>`. The persisted struct carries:
1. `schema_version: u32` envelope (Decision 34) — explicit version handshake.
2. Structural declarations (`imports`/`exports`/`platforms`/`submodules`) preserved as the **original specification** in source order (Decision 33 / Step 5a) — `src/save.rs::generate_module_source` reads them directly without reconstruction.
3. Per-symbol resolved entries (`ModuleEntry::Def { ast, scheme, got_slot, callees, … }`, `ModuleEntry::Import { source }`, etc.) — the resolved effects of typecheck.
4. Runtime fields (`code`, `platform_fn_ptr`, `got`, `linker`) all `#[serde(skip)]` — cache-restore re-derives `code` by re-running codegen against `ast` (per §14.3 step [5b]) and `platform_fn_ptr` by re-resolving the DLL named in the persisted `PlatformDecl` (per Decision 26). The `Arc<Jit>` lives directly on `code` per Decision 31 Scenario 2 (Step 5c activated generics).

**Divergence rationale — load-bearing structural separation**: the sketch's lack of separation between "structural specification" and "resolved effects" produced two specific problems that Decision 33 + the Step 5b shape both fix:
1. **`.cl` regeneration was lossy.** Spec §6.4 requires `(read-source <module>)` to round-trip the original imports/exports/platforms/mods in source order. The sketch reconstructed them by walking `ModuleEntry::Import` chains, which lost grouping (a single `(import [foo [a b c]])` form might have produced three separate `Import` entries depending on the resolution path), source order (the ordering came from HashMap iteration), and the distinction between explicit name lists and `(import [foo [*]])` glob form. Decision 33's structural-decl fields preserve the originals; the resolved entries continue to live as `ModuleEntry::Import`.
2. **Cache reads needed parallel rebuild logic.** The sketch's `try_load_cached_module()` had to re-run import resolution (rebuilding the `Import` entries from the persisted `import_specs`), trait registration (rebuilding `TraitRegistry` entries from persisted impls), and macro registration. Each rebuild was a 30–80 line loop that could (and did) drift from the fresh-build path. Step 5b's design eliminates the rebuild loops: deserialise gives both the structural decls AND the resolved entries directly; the import resolver, trait registrar, and macro registrar all read from the SymbolTable they already operate on during fresh build (`install_module_scope()` is the shared call site). One code path, two callers. (This is the structural fix for sketch finding MED-2.)

The Decision-25 / Decision-31 placement of `code` / `Arc<Jit>` directly on `ModuleEntry::Def.code` (vs the sketch's pattern of holding code pointers in a session-side `def_codegen: HashMap<Symbol, DefCodegen>` parallel store) is the third structural divergence. The sketch's parallel store contained MED-2 + LOW-1 + LOW-3 audit findings stemming from the same root cause: when "compiled code" lives in a parallel store, cache-restore has to write into that parallel store from the deserialised metadata, and the write path is inevitably different from the fresh-build write path. With code on the entry, both paths use the same write site.

The sketch's `CacheCodegenState` (a serializable subset of `ModuleCodegenState` invented at Sprint 22 to give cache something to persist) dissolves entirely in the v4 shape because there is no `ModuleCodegenState` — `SymbolTable` IS the storage, and its `#[serde(skip)]` fields cover the runtime state. This is the cleanest Principle 7 (single source of truth) outcome for the cache subsystem.

**What the v4 cache keeps from the sketch (unchanged, validated)**:
- Module-granular caching (sketch goal 1 / spec §8.10.3).
- Background-thread cache writes (sketch goal 5 — REPL responsiveness).
- Atomic file writes via temp-file-then-rename (sketch goal 3).
- Manifest-based O(1) cache-hit checks (sketch §3.3).
- Source-content-hash invalidation (sketch §3.1).
- Transitive dependency hash check (sketch §3.2).
- The dual JIT/ObjectModule generation strategy (§5) — though now via single `compile_to_module<M: Module>` per Decision 23.
- Linker for `.o` loading in `--link` mode (sketch's `linker.rs`).

The v4 shape is a structural cleanup of the sketch's cache, not a re-design of the cache concept. The sketch's invariants are preserved; the encoding is changed to remove the parallel stores and gain explicit version handshaking.

### 14.9 Cross-references

- `design/int/symbol-table-cache.md` — `/int`-owned producer-side companion. Documents the worker cache-write trigger, background-thread coordination, and call into `/backend`'s cache-write helper. MUST agree with this section on the `CACHE_SCHEMA_VERSION` constant name + location.
- `design/arch/CLAUDE.md` Decisions 25, 26, 31, 32, 33, 34 — the architectural foundation for §14's design choices.
- `design/arch/interfaces.md` §"Symbol Table" + §"Module Entries" — the parameterised `SymbolTable<C, L>` and `ModuleEntry<C>` shapes; the schema-version field.
- `design/arch/pipeline-v4.md` §9.5 — the §9 target normative form ("the `.meta.json` file is a serialized `SymbolTable`").
- `design/backend/compile-to-module.md` §17 (Step 5c) — the parameterised signature shape `compile_to_module` consumes; cache-restore step [5b] in §14.3 calls into `compile_to_module<JITModule>`.
- `design/typecheck/ast-annotation.md` — the per-category contract for which `ModuleEntry` entries carry `ast: Some(_)`; cache-restore relies on the same contract.
- `crates/cranelisp-backend/src/cache/mod.rs` — `CACHE_SCHEMA_VERSION` constant location.
- `crates/cranelisp-backend/src/cache/serialize.rs` — file targeted for rewrite (the `CacheMetadata` / `CacheCodegenState` types either dissolve or shrink to a thin `CacheEnvelope`).
