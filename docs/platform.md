# Platform: Dynamic Loading Design

## 1. Motivation

Cranelisp separates platform effects (IO functions like `print`, `read-line`) from the language runtime. All platform functions come from dynamically-loaded platform libraries (`.dylib`/`.so`/`.dll`). There is no built-in default — every module that uses IO must declare `(platform name)` and import the functions it needs.

Dynamic platform loading enables:

- **Test harnesses** — capture output, inject scripted input, assert on IO sequences without subprocess gymnastics
- **Web targets** — redirect IO to DOM nodes or WebSocket channels
- **Embedded** — platform-specific IO for microcontroller or bare-metal targets
- **Custom IO environments** — game engines, audio pipelines, database adapters, GUI event loops
- **User-extensible effects** — third-party platforms without forking the compiler

The existing architecture already separates platform from language internals cleanly (`docs/io.md:144-159`). Dynamic loading makes that boundary a runtime seam instead of a compile-time one.

## 2. Definitions

Three layers (established in `docs/io.md`):

```
┌─────────────────────────────┐
│  User code (cranelisp)      │  (defn main [] (print 42))
├─────────────────────────────┤
│  Platform (dynamic library) │  print : String -> IO Int, read-line : () -> IO String
├─────────────────────────────┤
│  Language (src/intrinsics.rs)│  alloc, free, panic : (internal, not in type env)
└─────────────────────────────┘
```

**Platform** — the set of `extern "C"` functions whose types have `IO` return wrappers. These implement effects visible to user code. All platforms are dynamically loaded cdylibs implementing the `cranelisp-platform` ABI contract. Path resolution and DLL loading is in `src/platform.rs`.

**Language runtime** — heap management (`alloc`, `free`), panic handler, reference counting machinery. Always linked into the host binary. Not visible to user code's type environment.

**Intrinsics** — inline codegen operations (arithmetic, comparisons, constructors). Part of the compiler, not externally loadable.

**Boundary rule**: a function belongs in the platform if and only if its return type is wrapped in `IO`. Everything else stays in the binary.

## 3. Feasibility

`Jit::new()` registers a `symbol_lookup_fn` closure backed by `Arc<Mutex<HashMap<String, SendPtr>>>`. When `Jit::load_platform()` is called, it inserts each platform function's JIT symbol and pointer into this dynamic map. The `JITModule` resolves external symbols lazily through this closure, so platforms can be loaded after module creation.

```rust
// In Jit::new():
let dynamic_symbols = Arc::new(Mutex::new(HashMap::<String, SendPtr>::new()));
let syms = dynamic_symbols.clone();
builder.symbol_lookup_fn(Box::new(move |name| {
    syms.lock().unwrap().get(name).map(|sp| sp.0)
}));

// Later, when loading a platform:
let (name, version, descriptors) = jit.load_platform(&dll_path)?;
// This inserts symbols into dynamic_symbols and declares functions on the module
```

The `extern "C"` all-`i64` calling convention (`docs/codegen.md`) is inherently DLL-compatible — no Rust ABI dependencies, no generics, no trait objects across the boundary.

Platform DLLs are stored in `Jit.loaded_libraries: Vec<Library>` to keep them alive for the JIT's lifetime.

## 4. Shared Interface Crate (`cranelisp-platform`)

A workspace member crate (`cranelisp-platform/`) that defines the platform contract in code. Both the cranelisp host binary and every platform DLL depend on this crate. It has no dependencies.

```
cranelisp/
├── cranelisp-platform/     # shared interface crate (ABI types, constants, macro)
│   ├── Cargo.toml
│   └── src/lib.rs
├── src/                    # host binary
│   ├── jit.rs
│   ├── platform.rs         # built-in stdio + re-exports + path resolution + descriptors
│   └── ...
└── platforms/              # platform DLLs (cdylib crates)
    ├── stdio/              # reference stdio platform
    │   ├── Cargo.toml
    │   └── src/lib.rs
    └── test-capture/       # test harness platform (in-memory buffers)
        ├── Cargo.toml
        └── src/lib.rs
```

The shared crate defines:

- `ABI_VERSION: u32` — bump on breaking changes (currently 1)
- `STRING_HEADER_BYTES: usize` — string layout constant (8 bytes for i64 length prefix)
- `PlatformFn` (`#[repr(C)]`) — function descriptor with name, jit_name, ptr, param_count, type_sig, docstring, and param_names (all as raw pointer + length pairs)
- `HostCallbacks` (`#[repr(C)]`) — host services passed to the platform at init (currently just `alloc`)
- `PlatformManifest` (`#[repr(C)]`) — manifest returned by the DLL entry point (abi_version, name, version, function descriptors)
- `declare_platform!` macro — generates the `extern "C" fn cranelisp_platform_manifest(...)` entry point

The host (`src/platform.rs`) re-exports the C-ABI types with aliased names (`PlatformFnC`, `HostCallbacksC`, `PlatformManifestC`) and provides `manifest_to_descriptors()` to convert the unsafe C-ABI manifest into safe Rust `OwnedPlatformFnDescriptor` values.

**Why a shared crate?** Without it, the host and platform must agree on struct layouts by convention — a silent ABI mismatch causes memory corruption. With the shared crate, any change to `PlatformManifest`, `PlatformFn`, or `HostCallbacks` is a compile-time error in both the host and every platform DLL. The crate is the contract.

## 5. Platform ABI Contract

All platform functions follow a uniform calling convention:

| Property | Value |
|---|---|
| Calling convention | `extern "C"` (SystemV on x86-64/aarch64) |
| Parameter types | All `i64` |
| Return type | `i64` |
| String representation | Pointer to `[i64 len][u8 bytes...]` |
| Heap layout | `[i64 size][i64 rc][payload...]` — pointer points to payload |
| Bool representation | `0` (false) / `1` (true) in `i64` |
| Float representation | `f64` bits stored in `i64` via bitcast |

This matches the existing convention used by `src/platform.rs` and `src/intrinsics.rs`.

### Manifest Entry Point

Every platform DLL exports exactly one function:

```c
extern "C" PlatformManifest cranelisp_platform_manifest(const HostCallbacks* callbacks);
```

The host calls this once at load time, receiving back the complete platform descriptor. The `callbacks` pointer provides host services (currently just the allocator) that the platform stores for later use.

All types (`PlatformManifest`, `PlatformFn`, `HostCallbacks`) are defined in the `cranelisp-platform` shared crate, ensuring binary compatibility at compile time.

## 6. Host Callbacks

Platform functions that return heap-allocated values (like `read-line` returning a String) need access to the host allocator. They cannot use their own allocator because the returned pointer must be compatible with the host's `free`/reference-counting machinery.

The `HostCallbacks` struct (from the shared crate) is passed to the manifest function. The platform stores the callback pointers and uses them in its function implementations:

```rust
// In the stdio platform DLL
use cranelisp_platform::HostCallbacks;

static mut HOST: *const HostCallbacks = std::ptr::null();

fn init(callbacks: *const HostCallbacks) {
    unsafe { HOST = callbacks; }
}

pub extern "C" fn read_line() -> i64 {
    let mut buf = String::new();
    std::io::stdin().read_line(&mut buf).unwrap_or(0);
    let trimmed = buf.trim_end_matches(&['\n', '\r'][..]);
    let bytes = trimmed.as_bytes();
    let size = 8 + bytes.len() as i64; // length prefix + payload
    let ptr = unsafe { ((*HOST).alloc)(size) };
    unsafe {
        *(ptr as *mut i64) = bytes.len() as i64;
        std::ptr::copy_nonoverlapping(
            bytes.as_ptr(),
            (ptr + 8) as *mut u8,
            bytes.len(),
        );
    }
    ptr
}
```

Current callbacks:

| Callback | Signature | Purpose |
|---|---|---|
| `alloc` | `extern "C" fn(i64) -> i64` | Allocate `size` bytes, returns payload pointer |

Future callbacks (added as needed):

| Callback | Signature | Purpose |
|---|---|---|
| `free` | `extern "C" fn(i64) -> i64` | Release allocation |
| `panic` | `extern "C" fn(i64) -> i64` | Report fatal error |

## 7. Module Metadata

Source files declare their platform with a top-level form using a bare symbol:

```clojure
(platform stdio)
(import [platform.stdio [*]])

(defn main []
  (print "hello"))
```

The `(platform name)` form loads the DLL and creates a `platform.<name>` module. A separate `(import ...)` brings the functions into scope. An optional explicit path can be given:

```clojure
(platform stdio "path/to/libcranelisp_stdio.dylib")
```

### Resolution Rules

1. **Explicit path** — if a second string argument is provided, use it directly
2. **Named lookup** — otherwise, search a platform path:
   ```
   ./platforms/<name>.<ext>
   ./target/debug/libcranelisp_<name>.<ext>    (Cargo development convenience)
   ./target/release/libcranelisp_<name>.<ext>
   ~/.cranelisp/platforms/<name>.<ext>
   ```
   Where `<ext>` is `.dylib` (macOS), `.so` (Linux), or `.dll` (Windows).
3. **Manifest name validation** — the declared name must match the DLL's manifest metadata

### REPL

In the REPL, `(platform name)` is intercepted and handled directly:

```
cranelisp> (platform stdio)
Loaded platform: stdio v0.1.0 (2 functions)
  Use (import [platform.stdio [*]]) to bring into scope
cranelisp> (import [platform.stdio [*]])
Imported: print, read-line
cranelisp> (print "hello")
hello
```

A `PlatformDecl` entry is stored in the current module's symbol table and appears in `/list` under the "Platforms" category.

## 8. Loading Sequence

```
Module graph build
    │
    ▼
extract_module_decls() finds (platform name) forms
    │
    ▼
For each platform declaration:
    │
    ▼
Resolve to DLL path (explicit or search)
    │
    ▼
load_platform_dll(path):
    ├── libloading::Library::new(path)
    ├── lib.get("cranelisp_platform_manifest")
    ├── Call manifest function with &HostCallbacks
    ├── Validate: abi_version == ABI_VERSION
    └── Validate: manifest name matches declared name
    │
    ▼
Jit::load_platform():
    ├── Insert (jit_name, fn_ptr) into dynamic_symbols map
    ├── declare_platform_functions_owned() → create FuncIds
    └── Push Library into loaded_libraries
    │
    ▼
TypeChecker::register_platform():
    ├── Create platform.<name> CompiledModule
    ├── Parse each function's type_sig
    ├── Validate: return type wrapped in IO
    └── Insert Def entries with DefKind::Primitive
    │
    ▼
populate_builtin_func_ids() → backfill FuncIds
    │
    ▼
Compilation proceeds normally (import brings names into scope)
```

Platform loading happens before the module compilation loop, so all platform functions are available to all modules in the graph.

## 9. JIT Integration

Platform functions are dispatched through the module system using resolution-based lookup, not hard-coded names or dedicated FuncId fields.

### Registration

`Jit::new()` creates an empty JIT module with a `symbol_lookup_fn` closure backed by `dynamic_symbols: Arc<Mutex<HashMap>>`. No platform functions are loaded at construction time.

`Jit::load_platform(path)` loads a DLL, inserts each function's `(jit_name, fn_ptr)` into the dynamic symbols map, and calls `declare_platform_functions_owned()` to create `FuncId`s on the JIT module. The `Library` handle is stored in `loaded_libraries: Vec<Library>` to keep the DLL alive.

The `Jit` struct has no platform-specific FuncId fields. It holds only language runtime FuncIds (`alloc_func_id`, `panic_func_id`, `free_func_id`) and the general `builtin_methods` map (for extern primitives and operator wrappers).

### Dispatch

Platform function calls are resolved during type checking. The typechecker emits `ResolvedCall::BuiltinFn(FQSymbol)` for calls to platform functions (and extern primitives). At codegen time (`apply.rs`), the `BuiltinFn` variant looks up the `FuncId` from the target module's `CompiledModule` entry:

```rust
ResolvedCall::BuiltinFn(fq) => {
    if let Some(cm) = self.modules.get(&fq.module) {
        if let Some(ModuleEntry::Def {
            kind: DefKind::Primitive { func_id: Some(fid), .. }, ..
        }) = cm.get(fq.symbol.as_ref())
        {
            let local = self.module.declare_func_in_func(*fid, self.builder.func);
            let call = self.builder.ins().call(local, &arg_vals);
            return Ok(self.builder.inst_results(call)[0]);
        }
    }
}
```

After JIT initialization, `populate_builtin_func_ids()` backfills `FuncId`s onto all `DefKind::Primitive` entries that carry a `JitSymbol`. This bridges the gap between type registration (which creates module entries) and JIT module creation (which assigns FuncIds).

Adding a new platform function requires no codegen changes — only a new descriptor in the platform's manifest.

## 10. Type Integration

Each `PlatformFn` in the manifest carries a `type_sig` field — an S-expression string representing the cranelisp type:

```
"(Fn [String] (IO Int))"     ← print
"(Fn [] (IO String))"        ← read-line
```

At load time, the host:

1. Parses each type signature using the existing S-expression reader (`src/sexp.rs`)
2. Converts it to a `Type` via the type-from-sexp machinery
3. Validates: return type must be wrapped in `IO` (platform boundary rule)
4. Validates: all referenced types exist in the type environment
5. Registers the function in the typechecker's environment

```rust
// Pseudocode for platform type registration
for func in manifest.functions() {
    let type_sexp = parse_sexp(func.type_sig_str())?;
    let ty = type_from_sexp(&type_sexp)?;
    validate_io_return(&ty)?;
    typechecker.register_builtin(func.name_str(), ty);
}
```

This ensures that platform functions participate fully in type inference. Misspelled type names or missing `IO` wrappers are caught at platform load time, not during compilation.

## 11. No Built-in Default

There is no built-in platform. `Jit::new()` registers only intrinsics (alloc, free, panic), inline primitives, and extern primitives. Platform functions are available only after an explicit `(platform name)` declaration and `(import [platform.<name> [*]])`.

`src/platform.rs` provides path resolution (`resolve_platform_path`), DLL loading helpers (`load_platform_dll`), the `OwnedPlatformFnDescriptor` type, and the `manifest_to_descriptors()` converter. It re-exports C-ABI types from the `cranelisp-platform` shared crate.

The standard library (`lib/core.cl`, `lib/prelude.cl`) is platform-independent — it does not import or re-export any platform functions. Modules that need IO declare their own platform:

```clojure
;; examples/hello.cl
(platform stdio)
(import [platform.stdio [*]])
(defn main [] (print (show 42)))
```

## 12. Versioning & Compatibility

### ABI Version

The `ABI_VERSION` constant in the shared crate is the single source of truth. The host checks `manifest.abi_version == ABI_VERSION` at load time and rejects mismatches with a clear error:

```
Error: platform "audio" requires ABI version 2, but this cranelisp binary supports version 1.
Rebuild the platform against the current cranelisp-platform crate.
```

### DLL Naming Convention

Two naming patterns are searched:

1. **Plain**: `<name>.<ext>` — searched in `./platforms/` and `~/.cranelisp/platforms/`
2. **Cargo**: `libcranelisp_<name>.<ext>` — searched in `./target/debug/` and `./target/release/`

Where `<ext>` is platform-dependent: `.dylib` (macOS), `.so` (Linux), `.dll` (Windows). The `(platform name)` form uses a bare symbol; the host appends the correct extension and prefix.

### What the ABI Version Covers

- `PlatformManifest` struct layout
- `PlatformFn` struct layout
- `HostCallbacks` struct layout
- Calling convention (`extern "C"`, all `i64`)
- String representation (`[i64 len][u8 bytes...]`)
- Heap layout (`[i64 size][i64 rc][payload...]`)

The shared crate encodes all of these. Changing any of them requires a version bump.

## 13. Security

Loading a platform DLL means running arbitrary native code. This is equivalent to linking a C library — there is no sandboxing.

### Trust Model

- **Explicit declaration**: the `(platform "name")` form in source code makes the dependency auditable
- **No implicit loading**: omitting the form uses the built-in platform, which is part of the compiler binary
- **Filesystem paths are explicit**: `(platform "./untrusted.dylib")` makes the risk visible in source
- **No network loading**: platforms are local files only

### Recommendations for Users

- Audit platform source code before use
- Prefer well-known, published platforms
- Pin platform versions in project configuration
- In sensitive environments, restrict the platform search path

## 14. Migration Phases

All phases are complete.

| Phase | Description | Breaking Changes |
|---|---|---|
| **0. Unified dispatch** | **COMPLETE.** `DefKind`/`DefCodegen` narrow `ModuleEntry::Def`. `ResolvedCall::BuiltinFn` + `JitSymbol` enable resolution-based dispatch through module entries. `print_func_id`/`read_line_func_id` eliminated from codegen pipeline. | None |
| **1. Scoped platform module** | **COMPLETE.** Synthetic `platform` renamed to `platform.stdio`. `SYNTHETIC_MODULES` array replaced with `is_synthetic_module()` function supporting `platform.*` namespace. | None |
| **2. Abstract platform interface** | **COMPLETE.** `Jit::new()` refactored to data-driven registration via `builtin_stdio_platform()` descriptors. `apply.rs` uses `ResolvedCall::BuiltinFn` for dynamic module-entry-based lookup. | None (same behavior) |
| **3. DLL loading infrastructure** | **COMPLETE.** `libloading` dependency added. C-ABI contract types (`PlatformFnC`, `HostCallbacksC`, `PlatformManifestC`, `OwnedPlatformFnDescriptor`) in `platform.rs`. `Jit::with_platform()` loads DLL, validates ABI version, extracts descriptors. Path resolution (`resolve_platform_path`) searches `./platforms/` and `~/.cranelisp/platforms/`. `TypeChecker::register_platform()` parses type sigs, validates IO return, creates scoped module. | None (additive) |
| **4. Source syntax** | **COMPLETE.** `(platform "name")` parsed in `extract_module_decls()` (module.rs). `ModuleDecls.platforms` and `ModuleInfo.platforms` carry declarations through the module graph. AST builder errors if form leaks through. Batch mode (`run_project`) and REPL (`run_with_file`) validate entry module platforms: `"stdio"` and absent are accepted; unknown names error with `resolve_platform_path` lookup. | None (new form, existing code unaffected) |
| **5. Workspace + stdio DLL** | **COMPLETE.** Cargo workspace with `cranelisp-platform/` shared interface crate (ABI types, constants, `declare_platform!` macro) and `platforms/stdio/` cdylib. C-ABI types moved from `platform.rs` to shared crate; host re-exports with aliased names. `manifest_to_descriptors()` free function converts C-ABI manifest to safe Rust descriptors. Stdio DLL implements `print` and `read-line` using host allocator via `HostCallbacks`. Batch and REPL attempt DLL loading when `resolve_platform_path` finds a match; `"stdio"` falls back to built-in when no DLL found. `ReplSession::with_jit()` constructor enables pre-built JIT injection. | None |
| **6. Test-capture platform** | **COMPLETE.** `platforms/test-capture/` cdylib replaces stdio with in-memory buffers: `print` captures output to a `Mutex<Vec<String>>`, `read-line` returns pre-configured lines from a `Mutex<VecDeque<String>>`. Test utility exports (`test_capture_set_input`, `test_capture_get_output`, `test_capture_free_output`, `test_capture_reset`) accessed from Rust tests via `libloading`. 9 integration tests in `tests/platform.rs` cover DLL loading for both stdio and test-capture, manifest validation, ABI version checking, print capture, multi-line output, scripted input injection, multiple reads, state reset, and empty-input edge case. Tests run with `--test-threads=1` due to global DLL state. `just test-platform` recipe builds DLLs and runs platform tests; main `just test` recipe includes platform tests. | None |
| **7. No built-in default** | **COMPLETE.** Removed built-in stdio from `Jit::new()`. All platforms load exclusively via DLL. `Jit` uses `symbol_lookup_fn` closure with `dynamic_symbols: Arc<Mutex<HashMap>>` for post-construction symbol registration. `Jit::load_platform()` replaces `Jit::with_platform()`. `(platform name)` syntax uses bare symbol (not string). Standard library (`lib/core.cl`, `lib/prelude.cl`) is platform-independent. All examples declare `(platform stdio)` + `(import [platform.stdio [*]])`. REPL intercepts `(platform ...)` directly and creates `ModuleEntry::PlatformDecl` in the declaring module. `/list` shows "Platforms" category. Platform search includes `target/debug/` and `target/release/` for Cargo development. | Breaking: programs must declare `(platform stdio)` and import explicitly |

## 15. Future Extensions

### Multiple Platforms

A module can load multiple platforms, each creating its own namespaced module:

```clojure
(platform stdio)       ; creates platform.stdio
(platform network)     ; creates platform.network
(import [platform.stdio [print]])
(import [platform.network [http-get http-post]])
```

The standard import/module system handles namespacing — no special conflict resolution needed. If two platforms export the same name, the user imports them selectively or uses qualified names.

### Platform-Specific Opaque Types

Platforms could define opaque types that user code manipulates but cannot inspect:

```clojure
;; network platform provides:
;; connect : String -> IO Connection
;; send : Connection -> String -> IO Int
;; close : Connection -> IO Int
```

`Connection` would be an opaque handle (an i64 index into platform-internal state). The type signature in the manifest declares it; the typechecker tracks it; the platform manages the underlying resource.

### Hot Reloading

The per-module GOT design (`docs/modules.md:245-258`) already supports incremental recompilation. Platform functions could be registered in a GOT slot rather than via `Linkage::Import`, enabling platform hot-reload:

1. Load new DLL version
2. Update GOT entries for platform functions
3. Next call picks up new implementation automatically

This piggybacks on the same mechanism that enables module hot-reload.

### Roc-Style Task Return Model

Currently, effects execute eagerly (`docs/io.md:161-165`). A future extension could let `main` return a `Task` description that the platform interprets:

```clojure
;; Future: main returns a Task, platform executes it
(defn main []
  (Task.sequence
    [(Task.print "hello")
     (Task.read-line)]))
```

This would require the platform to provide a task runner, and cranelisp to support Task as a built-in type. The DLL mechanism is compatible — the platform would export a `run_task` function alongside the individual effect functions.

## 16. Open Questions

| Question | Context |
|---|---|
| **Allocator sharing scope** | Currently `HostCallbacks` exposes `alloc`. Should it also expose `free`? Platforms might need to free strings they receive as arguments (currently they don't, but future platforms might need to). |
| **Error propagation** | How should a platform function signal an error? Currently `print` returns 0; `read-line` panics on failure. Options: return error codes in i64, use the host panic callback, return `Result`-like tagged values. |
| **Cross-platform DLL extensions** | The host currently appends `.dylib`/`.so`/`.dll` based on `cfg!(target_os)`. Should platform authors ship fat packages, or should the build system handle this? |
| **AOT compilation interaction** | `ROADMAP.md` lists AOT compilation as a medium-term goal. With AOT, platform DLLs would be linked at compile time (static or dynamic). The manifest mechanism still works — the AOT compiler reads the manifest and emits appropriate relocations. |
| **Workspace structure** | Resolved: `cranelisp-platform` is a workspace member in the same repo. Third-party platform authors can depend on it as a published crate in the future. |
| **Platform initialization** | Should the manifest function be called once at startup, or should platforms have explicit `init`/`shutdown` lifecycle hooks? Lifecycle hooks help platforms that manage resources (connections, file handles). |
| **Callback table evolution** | When `HostCallbacks` gains new fields, old platforms compiled against the smaller struct will read garbage. Options: version field in callbacks, nullable function pointers, or strict ABI version matching (simplest). |
