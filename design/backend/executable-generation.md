# Executable Generation

Design for standalone executable generation via `--link`. This extends the module caching pipeline (see `module-caching.md`) by linking cached `.o` files into a native binary.

## 1. Problem Statement

Cranelisp programs can be run interactively (REPL) or in batch mode (JIT compile and execute). Neither produces a persistent artifact — the user must have the Cranelisp compiler installed to run any program. `--link` adds a third mode: compile all modules (caching where possible), generate a startup stub, and invoke the system linker to produce a standalone native executable.

### Goals

1. **Zero runtime dependency**: the produced executable requires no Cranelisp installation.
2. **Cache reuse**: leverage the existing `.o` caching from Sprint 22 — `--link` should not recompile modules that are already cached and valid.
3. **Clear `main` requirement**: produce a helpful error if the entry module has no `main` function, before attempting to link.
4. **IO support**: handle both `main :: () -> Int` (exit code) and `main :: () -> IO _` (IO trampoline).

### Non-goals

- Cross-compilation (the executable targets the host platform only).
- Release-quality optimisation (that is Phase H, LLVM backend).
- Linux/Windows support (macOS aarch64 only for Ring 4; abstractable later).
- Stripping or code signing.

## 2. Sketch Comparison

### How the sketch does it

The sketch implements executable generation across two files:

- **`sketch/src/exe.rs`** (458 lines): startup stub generation (`generate_startup_object`), system linker invocation (`link_executable`), bundle library locator (`find_bundle_lib`), platform rlib locator (`find_platform_rlibs`), platform manifest name collector (`collect_platform_manifest_names`).
- **`sketch/src/batch.rs`** `build_executable()` (88 lines): orchestrates the pipeline — builds the module graph, runs the compilation pipeline (which writes `.o` cache files), collects `.o` paths from cache directories, generates the startup stub, finds the bundle library and platform rlibs, invokes the linker.

The sketch uses the `--exe [output] [file.cl]` CLI flag. The entry point is `batch::build_executable(entry_path, output_path)`.

### What worked

1. **Clean layering**: the existing compilation pipeline writes `.o` files as a side effect of batch compilation. `build_executable` just adds a post-compilation linking step — no pipeline changes needed.
2. **Cranelift-generated startup stub**: the startup `.o` is a small Cranelift `ObjectModule` that imports `main` and `exit`, avoiding any assembly or C dependency.
3. **Platform initialisation in the stub**: platform manifests are initialised before `main()` runs, so platform functions are available from the first line of user code.
4. **IO trampoline conditional**: the startup stub checks at compile time whether `main` returns `IO` and conditionally routes through `cranelisp_run_io`.

### What the sketch does poorly

1. **Hardcoded macOS aarch64**: `arm64`, `xcrun`, macOS `ld` flags are not abstracted.
2. **No `main` type validation before linking**: the sketch checks `.o` existence but does not validate `main`'s type signature until runtime link errors appear.
3. **Relative path gymnastics**: `rel()` helper with CWD-relative paths is fragile.

### Where the reimplementation diverges

| Aspect | Sketch | Reimplementation | Rationale |
|---|---|---|---|
| **CLI flag** | `--exe [output]` | `--link` (or per `/int` decision) | More descriptive of the action. `/int` decides final name. |
| **Startup stub location** | `src/exe.rs` in monolithic crate | `src/exe/` in `cranelisp` binary crate, calls backend APIs | Startup stub is pipeline orchestration (it needs `CompiledModule` data). Backend provides `build_isa(is_pic: true)` and object compilation utilities. |
| **Platform abstraction** | Hardcoded macOS | `LinkerConfig` struct abstractable to Linux later | Architecture concern: abstractable from day one, even if only macOS is implemented. |
| **`main` validation** | Post-compilation `.o` existence check | Pre-link type signature check against `SymbolTable` | Clear error before invoking the linker. |
| **Paths** | CWD-relative with `rel()` | Absolute paths throughout | Avoid CWD sensitivity. |

## 3. End-to-End Flow

```
cranelisp --link examples/hello.cl
         │
         ▼
  ┌─────────────────┐
  │ Parse CLI flags  │  (/int: src/main.rs)
  └────────┬────────┘
           ▼
  ┌─────────────────────────────────┐
  │ Build module graph              │  Same as batch mode
  │ Determine project_root, lib_dir│
  └────────┬────────────────────────┘
           ▼
  ┌─────────────────────────────────┐
  │ Compile module graph (cached)   │  Reuse batch pipeline
  │ Writes .o + .meta.json per mod  │  Cache hits skip compilation
  └────────┬────────────────────────┘
           ▼
  ┌─────────────────────────────────┐
  │ Validate main exists            │  Check SymbolTable for `main`
  │ Determine main return type      │  IO vs Int
  └────────┬────────────────────────┘
           ▼
  ┌─────────────────────────────────┐
  │ Collect .o paths from cache     │  All modules in compile_order
  │ (project cache + lib cache)     │
  └────────┬────────────────────────┘
           ▼
  ┌─────────────────────────────────┐
  │ Generate startup stub .o        │  Cranelift ObjectModule
  │ Write to cache dir              │
  └────────┬────────────────────────┘
           ▼
  ┌─────────────────────────────────┐
  │ Locate bundle library           │  libcranelisp_exe_bundle.a
  │ Locate platform rlibs           │  platform.*.rlib
  └────────┬────────────────────────┘
           ▼
  ┌─────────────────────────────────┐
  │ Invoke system linker            │  macOS ld via ld_args
  └────────┬────────────────────────┘
           ▼
  ┌─────────────────────────────────┐
  │ Report success / error          │
  └─────────────────────────────────┘
```

## 4. Startup Stub Design

The startup stub is a Cranelift-generated `.o` file that defines the executable's entry point. It imports external symbols and calls them in sequence.

### Symbol `start` (exported)

The entry point symbol, referenced by the linker via `-e _start`. Signature: `() -> !` (never returns).

### Sequence

1. **Platform init** (conditional): for each platform manifest function, call `cranelisp_init_platform(func_addr(manifest_fn))`. This must happen before `main` because user code may call platform functions.
2. **Call `main()`**: the user's `main` function, which returns `i64`.
3. **IO trampoline** (conditional): if `main` returns `IO _`, call `cranelisp_run_io(main_result)` to force the IO task tree. This returns the exit code as `i64`.
4. **Truncate and exit**: `ireduce` the `i64` result to `i32`, then call `exit(i32)`. `exit` does not return.
5. **Trap**: unreachable instruction after `exit` — required by Cranelift as a block terminator.

### Imported symbols

| Symbol | Signature | Source |
|---|---|---|
| `main` | `() -> i64` | User's entry module `.o` |
| `exit` | `(i32) -> !` | libc (via `-lSystem`) |
| `cranelisp_run_io` | `(i64) -> i64` | `libcranelisp_exe_bundle.a` |
| `cranelisp_init_platform` | `(i64) -> ()` | `libcranelisp_exe_bundle.a` |
| `cranelisp_platform_manifest` | `() -> ...` | Platform `.rlib` (address taken, not called directly) |

### ISA construction

The startup stub needs its own ISA for `ObjectModule`. Following the reimplementation's single-ISA principle, this uses `build_isa(is_pic: true)` from the backend — the same function used for module `.o` generation. The sketch constructs a separate ISA here (HIGH-2 audit finding); the reimplementation avoids this.

### Output

The startup `.o` is written to the project cache directory as `<entry>-startup.o`. It is regenerated on every `--link` invocation (not cached) because it depends on runtime state (whether `main` returns IO, which platforms are loaded) that cannot be cheaply validated.

## 5. Linker Invocation

### macOS aarch64

The system linker is invoked as a child process:

```
ld -arch arm64 -dead_strip \
   -o <output> \
   -e _start \
   <startup.o> \
   <module1.o> <module2.o> ... \
   -L<bundle_dir> -l<bundle_name> \
   -force_load <platform1.rlib> ... \
   -platform_version macos 14.0 14.0 \
   -lSystem \
   -syslibroot <xcrun --show-sdk-path>
```

Key flags:
- `-e _start`: entry point is the startup stub's `start` symbol (linker prepends underscore for Mach-O).
- `-dead_strip`: remove unused symbols. Important because the bundle library contains all runtime symbols but the program may not use all of them.
- `-force_load <rlib>`: platform rlibs must be force-loaded because their symbols are referenced by name (not by direct relocation), so the linker would otherwise strip them.
- `-lSystem`: links `libSystem.dylib` which provides `exit`, `mmap`, `mprotect`, and other system calls.
- `-syslibroot`: SDK path from `xcrun --show-sdk-path`. Required by modern macOS `ld`.
- `-platform_version macos 14.0 14.0`: required by modern `ld` to avoid warnings.

### LinkerConfig abstraction

```rust
struct LinkerConfig {
    arch: String,           // "arm64"
    entry_symbol: String,   // "_start"
    platform: String,       // "macos"
    min_version: String,    // "14.0"
    sdk_version: String,    // "14.0"
}

impl LinkerConfig {
    fn for_host() -> Result<Self, CranelispError> { ... }
}
```

Only the macOS aarch64 variant is implemented initially. The abstraction exists so that Linux ELF support can be added later without restructuring.

### Sysroot detection

`xcrun --show-sdk-path` is called as a subprocess. If it fails (Xcode Command Line Tools not installed), a clear error message directs the user to install them.

## 6. Bundle Library

### What it is

`libcranelisp_exe_bundle.a` is a Rust static library (`crate-type = ["staticlib"]`) that bundles the Cranelisp runtime into a single archive. Standalone executables link against it instead of depending on the JIT runtime.

### What it contains

- **`cranelisp-runtime` symbols**: `cranelisp_alloc`, `cranelisp_dealloc`, `cranelisp_panic`, `cranelisp_run_io`, and all primitive functions (`cranelisp_add_i64`, `cranelisp_string_eq`, etc.).
- **`cranelisp-platform` contract types**: `HostCallbacks`, `PlatformManifest`.
- **`cranelisp_init_platform`**: the platform initialisation function called by the startup stub. This is defined in the bundle crate itself (not in runtime) because it bridges the platform manifest calling convention.
- **Rust standard library subset**: `std::process::exit`, allocator, etc. — included automatically by `staticlib` crate type.

### Build dependency

Users must build the bundle before using `--link`:

```bash
cargo build -p cranelisp-exe-bundle
```

The bundle `.a` appears in `target/debug/` or `target/release/`. The locator function searches:
1. `CRANELISP_BUNDLE_PATH` environment variable (for CI or custom layouts).
2. Same directory as the `cranelisp` binary (typical for `cargo run`).
3. Sibling directories under `target/` (debug/release).

If not found, a clear error directs the user to build it.

### Platform rlibs

Platform DLLs (e.g., `platform.io`) compile to both `.dylib` (for JIT) and `.rlib` (for static linking). The `.rlib` path is derived from the `.dylib` path by extension replacement. Platform rlibs are force-loaded to ensure their `#[export_name]` symbols are available.

## 7. `main` Validation

Before invoking the linker, validate that the entry module exports a `main` function with an acceptable type signature.

### Acceptable signatures

| Signature | Meaning |
|---|---|
| `main :: () -> Int` | Exit code returned directly |
| `main :: () -> IO _` | IO task tree; forced via `cranelisp_run_io`, inner value truncated to exit code |

### Validation sequence

1. After compilation, inspect the entry module's `SymbolTable` for a `Def` entry named `main`.
2. If absent: error `"entry module has no 'main' function"`.
3. If present, check the scheme's type:
   - `Fn([], Int)` — direct exit code.
   - `Fn([], ADT("IO", _))` — IO trampoline.
   - Anything else — error `"main must return Int or IO, found: <type>"`.
4. Pass the `main_returns_io` boolean to `generate_startup_object`.

This validation happens after the full compilation pipeline (because type information comes from typechecking) but before the linker is invoked (to avoid cryptic linker errors about missing symbols).

## 8. Crate Ownership

| Component | Crate | Skill |
|---|---|---|
| `generate_startup_object()` | `cranelisp` (binary) | `/int` |
| `link_executable()` | `cranelisp` (binary) | `/int` |
| `find_bundle_lib()` | `cranelisp` (binary) | `/int` |
| `find_platform_rlibs()` | `cranelisp` (binary) | `/int` |
| `main_returns_io()` | `cranelisp` (binary) | `/int` |
| `build_isa(is_pic: bool)` | `cranelisp-backend` | `/backend` |
| `libcranelisp_exe_bundle` | `cranelisp-exe-bundle` | `/platform` |
| CLI flag wiring | `cranelisp` (binary) | `/int` |

The startup stub generation and linker invocation live in the binary crate because they depend on pipeline state (`SymbolTable` data, platform module information) that is not available at the backend crate level. The backend provides the ISA builder and any shared object-file utilities.

## 9. Edge Cases

### Missing cache

If `.o` files are not found in the cache after compilation (e.g., macro-only modules that produce no `.o`), skip them silently. The linker will report unresolved symbols if a needed `.o` is missing — this surfaces as a linker error.

### Missing bundle library

If `libcranelisp_exe_bundle.a` is not found, report:
```
Error: could not find libcranelisp_exe_bundle.a — build it with
`cargo build -p cranelisp-exe-bundle` or set CRANELISP_BUNDLE_PATH
```

### Linker errors

If `ld` exits with non-zero status, capture stderr and report it wrapped in a `CranelispError::CodegenError`. Common causes:
- Missing symbols (a module's `.o` was not generated — usually a bug in cache/codegen).
- SDK not installed (`xcrun` fails).
- Architecture mismatch (running on x86_64 — not supported yet).

### `--no-cache` interaction

If `--no-cache` is passed alongside `--link`, modules are compiled fresh but still emit `.o` files to a temporary directory. The linker collects `.o` paths from this temporary directory instead of the persistent cache. This ensures `--link` always works, even without persistent caching.

### Output path default

If no output path is specified, derive it from the entry file:
- `cranelisp --link examples/hello.cl` produces `hello` (entry stem, no extension).
- `cranelisp --link examples/hello.cl -o myapp` produces `myapp`.

`/int` decides the exact CLI syntax.

## 10. Future Work

- **Linux ELF**: extend `LinkerConfig` with Linux-specific flags (`-dynamic-linker`, `-lc`, etc.).
- **Release mode (Phase H)**: LLVM backend produces optimised `.o` files; same linking step applies.
- **Incremental linking**: only re-link if any `.o` file is newer than the output executable.
- **Code signing**: macOS may require ad-hoc signing for executables (`codesign -s -`).
