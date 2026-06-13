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
- ~~Linux/Windows support (macOS aarch64 only for Ring 4; abstractable later).~~ **Linux aarch64 is now in scope (S80) — see §11.** Windows remains out of scope.
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

- ~~**Linux ELF**: extend `LinkerConfig` with Linux-specific flags.~~ **Designed in §11 (S80).**
- **Release mode (Phase H)**: LLVM backend produces optimised `.o` files; same linking step applies.
- **Incremental linking**: only re-link if any `.o` file is newer than the output executable.
- **Code signing**: macOS may require ad-hoc signing for executables (`codesign -s -`).

---

## 11. Linux aarch64 ELF support (S80)

The dev/CI host moved to a Mac-hosted **aarch64 Linux VM** (Ubuntu 26.04). On Linux the entire `--link` family fails at `LinkerConfig::for_host()` with *"standalone executable generation is only supported on macOS aarch64"* — ~38 tests (`link::*` ~9, `build_confidence::*` ~12, `spec_platforms_adt` ~8, `spec_platforms` ~4, plus linked `trace`/`cache`/`examples`/`stdlib_link`/`platform_errors`). This section designs the Linux ELF path. See `memory/linux-vm-baseline.md` for the environment baseline.

### 11.1 What is already host-correct (no change)

The audit found the macOS coupling is **confined to the linker driver in `src/exe.rs`**. The following already do the right thing on Linux and need no change:

| Concern | Why it already works on Linux |
|---|---|
| **Object file format** | `build_isa(is_pic)` (backend `cache/object.rs`) builds the ISA from `cranelift_native::builder()` — the *host* triple. On `aarch64-unknown-linux-gnu` cranelift-object emits **ELF** automatically; on macOS it emits Mach-O. No format flag is hardcoded. |
| **PIC / PIE** | `--link` object emission uses `build_isa(true)` ⇒ `is_pic = true`. PIC objects link cleanly into the **default `-pie` executable** that modern Ubuntu's `cc` produces — no `-no-pie` needed, no `R_AARCH64_*` "recompile with -fPIC" errors. (The JIT path's `build_isa()`/`is_pic=false` is unaffected — different code path.) |
| **Platform DLL extension** | `platform.rs::PLATFORM_EXT` already has `#[cfg(target_os = "linux")] = "so"`. The *runtime* `(platform …)` DLL-load path (REPL/`--run`) is not part of this gap. |
| **Bundle artifact name** | `staticlib` crate-type ⇒ `libcranelisp_exe_bundle.a` on both macOS and Linux. `find_bundle_lib()` already searches for `.a`. (Already built on the VM.) |
| **Startup-stub Cranelift IR** | The stub's body (init-primitives → platform init → layout-hash gate → call main → IO trampoline → `exit`) is platform-neutral CLIF. Only its **exported symbol name** and the **entry strategy** change (§11.3). |

So the work is: (a) a Linux branch of `LinkerConfig`, (b) a Linux branch of `link_executable()` that drives `cc` instead of Apple `ld`, (c) the crt-entry symbol rename (§11.3), (d) Linux platform static-linking (§11.5, the hard part). Items (a)–(c) are `src/exe.rs` — **binary crate, `/int`-owned** per §8; `/backend` owns this design + `build_isa`. Item (d) may pull in `/platform`.

### 11.2 The macOS-specific surface (exhaustive)

Three functions in `src/exe.rs`:

1. **`LinkerConfig::for_host()`** — the gate. Returns macOS config (`arch:"arm64"`, `entry_symbol:"_start"`, `platform:"macos"`, version strings) or the error.
2. **`link_executable()`** — assembles Apple-ld64 args: `-arch arm64`, `-dead_strip`, `-e _start`, `-platform_version macos …`, `-lSystem`, `-syslibroot …`, `-force_load`. Invokes bare `ld`.
3. **`get_sdk_sysroot()`** — `xcrun --show-sdk-path` (macOS-only tool).

Plus two hardcoded symbol names that become host-dependent (§11.3): the stub's `declare_function("start", Export, …)` and `generate_main_alias_object`'s `main` export.

### 11.3 Entry-point strategy — the one real design decision

**macOS bypasses the C runtime.** It defines its own `start`, links with `-e _start`, and calls libc `exit()` directly via `-lSystem`. This is safe because on macOS **dyld initialises libSystem (malloc, errno-TLS, stdio) before jumping to the entry point**, regardless of crt.

**On Linux, glibc is initialised by `__libc_start_main`, which is called by crt's `_start` (from `Scrt1.o`) — not by the dynamic loader.** A custom ELF entry point that bypasses crt therefore runs with **uninitialised glibc**: the main-thread TLS block (`TPIDR_EL0`) is unset, so `errno`, `malloc`'s per-thread cache, and stdio are broken. The bundle links Rust `std`, whose `System` allocator calls `malloc` — so heap allocation (every `cons`, string, ADT) would crash. **Bypassing crt on Linux is not viable.**

**Decision: on Linux, route through crt by emitting the startup stub as C `main`.** The flow becomes the standard native one:

```
kernel → _start (Scrt1.o) → __libc_start_main  [glibc init: TLS, malloc, stdio]
       → main  (our startup stub)  → cranelisp_user_main (alias → GOT → user main)
       → exit(code)
```

This forces a **two-symbol rename, host-conditional**:

| Symbol | macOS (Mach-O, custom entry) | Linux (ELF, crt entry) |
|---|---|---|
| Startup-stub export (kernel/crt entry) | `start` (linked `-e _start`) | **`main`** (crt calls it; no `-e`) |
| User-main alias export / stub's import (`entry_fn_name`) | `main` | **`cranelisp_user_main`** (renamed to avoid colliding with the C `main`) |

Both names are read from `LinkerConfig` so `generate_startup_object` and `generate_main_alias_object` stop hardcoding them. The stub keeps calling `exit(code)` and trapping after — valid under crt (glibc is up by the time `main` runs); the trailing `trap` stays unreachable. The stub's zero-param/zero-return CLIF signature is ABI-safe as `main`: crt passes `argc/argv/envp` in `x0/x1/x2`, which we ignore (AAPCS caller-cleanup), and we never return (we `exit`).

> **No leading underscore on ELF.** cranelift-object emits the symbol verbatim on ELF (`main`), and adds the Mach-O `_` only on macOS. So `declare_function("main", Export, …)` on Linux yields ELF symbol `main` — exactly what crt references.

### 11.4 Linux linker invocation — drive `cc`, not bare `ld`

Use the **`cc` (gcc) driver**, not bare `ld`. The driver supplies what macOS's `-lSystem`/`-syslibroot` bundled implicitly: the crt objects (`Scrt1.o`, `crti.o`, `crtn.o`), the dynamic-linker path (`-dynamic-linker /lib/ld-linux-aarch64.so.1`), the default lib search paths, and `libc`/`libgcc`. Hand-assembling those with bare `ld` is brittle across distros; the driver is the portable choice.

Flag mapping:

| Purpose | macOS (`ld`) | Linux (`cc` driver) |
|---|---|---|
| Output | `-o out` | `-o out` |
| Entry point | `-e _start` | *(omit — crt's `_start` is the default entry; our `main` is found by crt)* |
| Arch | `-arch arm64` | *(implicit from host `cc`; `aarch64-linux-gnu`)* |
| Dead-strip | `-dead_strip` | `-Wl,--gc-sections` *(optional; see note)* |
| Force-load archive | `-force_load <rlib>` | `-Wl,--whole-archive <a> -Wl,--no-whole-archive` (§11.5) |
| System libc | `-lSystem` | *(driver adds `-lc`)* + explicit `-lpthread -ldl -lm` for Rust std |
| SDK root | `-syslibroot $(xcrun …)` | *(none — `get_sdk_sysroot` is not called on Linux)* |
| Platform version | `-platform_version macos …` | *(none)* |
| Fast linker | *(n/a)* | `-fuse-ld=mold` *(optional; mold present on VM)* |

Concrete Linux command:

```
cc -o <output> \
   <startup.o> <module1.o> … <alias.o> \
   -Wl,--whole-archive <platform1-objs.o…> … -Wl,--no-whole-archive \
   -L<bundle_dir> -l<bundle_name> \
   -lpthread -ldl -lm \
   -Wl,--gc-sections
```

(Phase 2: the `--whole-archive` group holds the **extracted `.o` members** of each platform `.rlib`, not the raw `.rlib` — see §11.5 — and is emitted **before** the bundle `-l` so GNU `ld` can resolve the platform objects' workspace references against the bundle archive.)

Notes:
- **Rust-std externs.** The bundle `.a` embeds Rust `std`, but std's *external* deps must be satisfied at final link: `-lpthread -ldl -lm` (the driver adds `-lc`/`-lgcc_s`). **Confirmed empirically (S80 Phase 1, Ubuntu 26.04 aarch64, gcc 15.2):** `-lpthread -ldl -lm` is sufficient — `cranelisp --link examples/01-integers.cl` links and runs cleanly (exit 69) with no unresolved symbols. `-lrt`/`-lutil` were NOT needed on this glibc. The final Linux arg list is exactly:
  ```
  cc -o <out> <startup.o> <module.o…> <alias.o> \
     [-Wl,--whole-archive <platform-objs.o…> -Wl,--no-whole-archive] \
     -L<bundle_dir> -l<bundle> \
     -lpthread -ldl -lm
  ```
  `--gc-sections` and `-fuse-ld=mold` are omitted (not needed for correctness; the basic path is green without them). The optional platform whole-archive group (Phase 2, §11.5) precedes the bundle `-l` — the GNU-ld static-archive link-order constraint.
- **`--gc-sections` is optional for the first cut.** It maps `-dead_strip` but is not required for correctness; the `main`, the GOT data symbols (Export, referenced by the alias), and `cranelisp_init_primitives` (referenced by the stub) are all reachable and retained. Add it after the basic path is green to avoid masking a real "missing reference" bug as a strip.
- **The produced executable does NOT need `-rdynamic`.** Its GOT is populated by the direct call to `cranelisp_init_primitives` in the stub (not `dlsym(RTLD_DEFAULT)`), and platform dispatch is direct calls. (`-rdynamic` is needed only for the *JIT test-harness* binary's in-process cache-restore path — a different binary, set machine-locally in `~/.cargo/config.toml`. Do not conflate.)

### 11.5 Platform static linking — the `.rlib` whole-archive hazard (Phase 2)

macOS `-force_load <platform>.rlib` pulls in the platform's `#[export_name]` GOT/manifest/layout-hash symbols. The GNU equivalent is `--whole-archive`. **But a Rust `.rlib` is an `ar` archive containing object members *plus* a `lib.rmeta` metadata member.** Under `--whole-archive`, GNU `ld` tries to link **every** member as an object and chokes on `lib.rmeta` ("file format not recognized"). Apple `ld64` tolerates this; GNU `ld`/mold may not.

Resolution options (decided during Phase-2 implementation):

1. **Extract object members from the rlib** and pass only the `.o`s to `--whole-archive`. Robust, no crate-type change. `ar t`/`ar x` (or the `object`/`ar` crate) lists members; skip `lib.rmeta` and `*.rmeta`. **Recommended default.**
2. **Build a `staticlib` (`.a`) per platform for `--link`** (mirroring `exe-bundle`). No rmeta member, self-contained, links with plain `--whole-archive`. Cleaner long-term but a `/platform` crate-type/build change and a second artifact to locate.
3. **Probe mold's leniency** — mold *may* skip non-object archive members. Cheapest to try; do not rely on it as the design.

**IMPLEMENTED (S80, option 1).** `src/exe.rs::extract_rlib_objects(rlib, cache_dir)` shells out to the system `ar` (already on the Linux toolchain — no `ar`/`object` crate added):

- **List:** `ar t <rlib>` prints one member per line.
- **Member-filter rule:** keep only members whose name **ends in `.o`** (the `*.rcgu.o` codegen units). This drops the rmeta family — `lib.rmeta` and its `lib.rmeta-link` sidecar — which do not end in `.o`. Empty object set ⇒ hard error.
- **Extract:** `ar --output=<dir> x <rlib> <member…>` extracts just the kept members into a **deterministic** per-rlib dir `<cache>/__plat_<rlib-stem>/` (the cache dir is `startup_o_path.parent()`, where `session_v4.rs` already writes `__startup.o`/`__main_alias.o`). The dir is cleared and recreated each link so a rebuilt rlib leaves no stale members. The extracted `.o` paths replace the raw `.rlib` inside the `-Wl,--whole-archive … -Wl,--no-whole-archive` group.

**Link-order requirement (§11.4 amendment).** The whole-archive platform objects MUST be emitted **before** the runtime bundle `-l<bundle>`, not after. A platform object references workspace symbols defined in the bundle (e.g. `cranelisp_platform::adt::set_global_schema`); GNU `ld` resolves a static archive (`.a`) only against symbols left **undefined by inputs seen so far**. With the bundle first, the later platform objects' fresh undefined refs would never be satisfied ("undefined reference to set_global_schema"). Placed before the bundle, the platform's undefined refs are open when the bundle is scanned. (macOS ld64 is order-insensitive here; this is a GNU-ld constraint.) The command order is therefore: `startup.o module.o… alias.o  -Wl,--whole-archive <plat.o…> -Wl,--no-whole-archive  -L<bundle_dir> -l<bundle>  -lpthread -ldl -lm`.

This is **Phase 2** and gates only the platform tests (`spec_platforms*`, `platform_errors` ~13). It landed after Phase 1. **Verified:** a `(platform stdio)` program (`(defn main [] (print "hello"))`) links and runs to `hello`/exit 0; `spec_platforms_adt::platform_stdio_print_link` (the R1 link-wiring guard) passes.

### 11.6 `LinkerConfig` redesign

Replace the flat macOS-only struct with a host-dispatched form carrying the **entry strategy** and **driver**:

```rust
enum LinkDriver { AppleLd, Cc }          // bare `ld` vs the gcc driver

struct LinkerConfig {
    driver: LinkDriver,
    stub_entry_symbol: &'static str,     // macOS "start"   | linux "main"
    user_main_symbol:  &'static str,     // macOS "main"    | linux "cranelisp_user_main"
    // macOS-only fields (unused on Linux):
    arch: Option<&'static str>,          // "arm64"
    platform_triplet: Option<(&'static str,&'static str,&'static str)>, // (platform,min,sdk)
}

impl LinkerConfig {
    fn for_host() -> Result<Self, CranelispError> {
        match (cfg!(target_arch = "aarch64"), std::env::consts::OS) {
            (true, "macos") => Ok(/* AppleLd, "start"/"main", arch+version */),
            (true, "linux") => Ok(/* Cc, "main"/"cranelisp_user_main" */),
            _ => Err(/* unchanged "only supported on …" message, widened */),
        }
    }
}
```

`generate_startup_object` and `generate_main_alias_object` take `stub_entry_symbol` / `user_main_symbol` from this config instead of the string literals `"start"`/`"main"`. `link_executable` matches on `driver` to build the two arg vectors and pick the child process (`ld` vs `cc`). `get_sdk_sysroot` is called only on the `AppleLd` arm.

### 11.7 Phasing & expected test recovery

| Phase | Scope | Clears (approx) |
|---|---|---|
| **1 — non-platform ELF** | §11.3 entry rename + §11.4 `cc` driver + Rust-std externs. No platform statics. | `link::*` (9), `build_confidence::*` (12), `trace` linked (2), `cache` (2), `examples` (1), `stdlib_link` (1), `s68_link` (1) — **~28** |
| **2 — platform statics** | §11.5 rlib object-extraction (or staticlib). | `spec_platforms_adt` (8), `spec_platforms` (4), `platform_errors` (1) — **~13** |

A handful outside the `--link` family (`repl_persist` 1, `regression` 1, `public_api_relocations` 1, `spec_10_io` 2) are **not** addressed here — they need separate triage and may be unrelated to executable generation.

### 11.8 Validation

Per the Release Gate, after implementation: `cargo nextest run -E 'test(/^link_/) + binary(link) + binary(build_confidence)'` should go green (Phase 1); the full suite should return to ≤ the macOS baseline of ~7 failures once Phase 2 lands (modulo the ~4 unrelated residue). A minimal smoke check during bring-up: `cranelisp --link examples/hello.cl && ./hello; echo $?` must produce the documented exit code. (`cc -fuse-ld=mold` was confirmed working on the VM: a 42-returning C `main` exits 42.)

### 11.9 Sketch comparison

Not consulted — the sketch is macOS-only here (the existing §2 comparison already covers its `generate_startup_object`/`link_executable`). The Linux entry-via-crt strategy and the `.rlib` whole-archive hazard are Linux-platform facts (glibc init model, Rust archive layout), not language-design questions, so the sketch offers no oracle. First-principles per CLAUDE.md.

---

## 12. The `Linker` abstraction (S80 Wave 2E) — intent in, platform tokens out

> **Status: TARGET design (S80 Wave 2E /arch ruling, 2026-06-13).** Replaces the §11.6 `LinkerConfig` + the parallel `link_executable_apple_ld` / `link_executable_cc` driver functions with a uniform `Linker` trait whose impls are the *sole* sites where platform tokens (`-force_load`, `--whole-archive`, `-arch`, `-dead_strip`, `/WHOLEARCHIVE:`) appear. `/dev` (int) implements the refactor; this section is the contract it implements against.

### 12.1 Why — bug D4 and the leak it exposed

The §11 Linux port added `link_executable_cc` (the GNU driver) alongside the macOS `link_executable_apple_ld`. The two functions are **parallel implementations**: each re-derives the same *linking intents* (force-load these platform archives so their export-name symbols survive; dead-strip; name the entry; emit the object list) in its own platform's flag syntax. Because the intents are not named anywhere — only their platform renderings exist — there is no single place that says "force-load the platform rlibs", and a maintainer touching one driver has no structural signal that a sibling site renders the same intent differently. Platform tokens leaked across **≥3 sites**:

1. **`link_executable_apple_ld`** (`src/exe.rs:723`) — emits `-force_load <rlib>` per platform rlib, plus `-arch arm64`, `-dead_strip`, `-platform_version`, `-syslibroot`, `-lSystem`, `-e _<entry>`.
2. **`link_executable_cc`** (`src/exe.rs:793`) — emits `-Wl,--whole-archive <extracted .o…> -Wl,--no-whole-archive` (the GNU rendering of the SAME force-include intent), plus `-Wl,--gc-sections` (the GNU rendering of dead-strip), the crt-implicit arch/libc.
3. **`log_link_summary`** (`src/exe.rs:1025`/`:1054`) — the diagnostic. It **hardcodes `-force_load <rlib>` regardless of driver** (`exe.rs:1054`), so on Linux the printed "command" shows macOS tokens that the real `cc` invocation never used. The diagnostic and the real command are two independent renderings that can (and did) drift.

**This leak IS the mechanism of bug D4.** A clean Linux full-workspace rebuild + the new `output_equivalence` link permutations exposed that the `--link` path was reaching `link_executable_apple_ld` (the `-force_load` driver) for a scenario on Linux, and GNU `ld.bfd` rejects `-force_load` → ~13 reds (12 `output_equivalence::*` link permutations + `platform_stdio_print_link`). The `git blame` dates `-force_load` to Sprint 23; the GNU `--whole-archive` path exists but the parallel-driver structure let the Linux port update one rendering and leave a sibling emitting the macOS token. A leak that the type system cannot catch, because the intent ("make platform export-name symbols survive the link") was never reified.

The fix is **by construction**: reify the intents as a `LinkRequest`, and make each platform's token-rendering the *sole responsibility* of one `Linker` impl. No platform token may appear outside a driver impl — including in the diagnostic, which renders the real command via the *same* path it executes.

### 12.2 `LinkRequest` — intent, no toolchain tokens

The caller (`session_v4.rs`) expresses *what to link and why*, never *how a toolchain spells it*. The request carries no `-force_load`, no `--whole-archive`, no `-arch`, no `-Wl,*` — those are driver renderings of these fields.

```rust
/// The bundle library to link against (the runtime `.a`): its directory and
/// its link name (the `lib`-stripped stem — e.g. `cranelisp_exe_bundle`).
struct BundleLib {
    dir: PathBuf,
    name: String,
}

/// A platform static archive whose `#[export_name]` symbols (GOT / manifest /
/// layout-hash) are referenced BY NAME at runtime, not by relocation, so a
/// normal link would dead-strip them. The linker MUST force every object of
/// this archive into the output. On GNU this is the *raw* `.rlib`; the GNU
/// driver is responsible for extracting its `.o` members (§12.5).
struct ForceIncludeArchive {
    rlib: PathBuf,
}

/// A native-link request expressed as intent. No platform/toolchain tokens.
struct LinkRequest {
    /// The startup-stub object (the executable entry: macOS `start`, Linux C `main`).
    startup_obj: PathBuf,
    /// Compiled module objects, including the user-main alias `.o` (caller-composed).
    module_objs: Vec<PathBuf>,
    /// The runtime bundle archive.
    bundle_lib: BundleLib,
    /// Platform archives whose export-name symbols must survive dead-strip.
    /// Empty for non-platform programs.
    force_include: Vec<ForceIncludeArchive>,
    /// The executable entry symbol the stub exports. macOS `"start"` (the driver
    /// adds the `-e _start` form); Linux `"main"` (crt's default entry — the
    /// driver omits `-e`). Carried as intent; the driver decides the flag.
    entry_symbol: String,
    /// Whether to dead-strip unused symbols. macOS `-dead_strip`; GNU
    /// `-Wl,--gc-sections`.
    dead_strip: bool,
    /// Output executable path.
    output: PathBuf,
}
```

Notes on the field set:

- **`entry_symbol` stays in the request, not the driver**, because the *value* (`start` vs `main`) is a host fact already computed by `host_entry_symbols()` and shared with `generate_startup_object` — it is the entry the stub actually exported, so the linker must reference the same name. The *flag form* (`-e _start` vs "omit, crt finds `main`") is the driver's. The macOS Mach-O underscore prefix is a driver rendering, NOT carried in the request.
- **`force_include` carries raw `.rlib` paths**, not pre-extracted `.o`s. Extraction is a GNU-specific rendering of the force-include intent (§12.5); the Apple driver force-loads the raw rlib directly. Pushing extraction into the request would leak a GNU concern into the caller.
- **No `arch` / `platform_triplet` / `sysroot` field.** These are macOS-`ld`-only renderings with no cross-platform meaning. They are constants internal to `AppleLdLinker` (it knows it is targeting `aarch64` macOS), fetched on demand (`get_sdk_sysroot()` lives inside the Apple impl). A future cross-arch story revisits this, but today they are not intent — they are Apple-ld syntax, and belong in the Apple driver.

### 12.3 The `Linker` trait

```rust
/// A native linker driver. Each impl is the SOLE place its platform's link
/// tokens appear. `link` executes; `describe` renders the same command for
/// diagnostics — both flow through the same arg-building path so the printed
/// command cannot drift from the executed one (the D4 fix).
trait Linker {
    /// Build the toolchain arg vector from the request and invoke the linker.
    fn link(&self, req: &LinkRequest) -> Result<(), CranelispError>;

    /// Render the command this impl WOULD run for `req`, as a human-readable
    /// string, for the `; Linking: …` diagnostic. MUST be produced from the
    /// same arg-building path `link` uses (see §12.6) — never an independent
    /// re-spelling.
    fn describe(&self, req: &LinkRequest) -> String;
}
```

**The `describe` discipline is the structural fix for the D4 class of bug** (Principle 18 — enforce invariants structurally; Principle 7 — single source of truth). `log_link_summary`'s hardcoded `-force_load` was a *second, drifting* rendering of the link command. By making `describe` a trait method that each impl produces from its own `link` arg-builder, the diagnostic for a given host is generated by the same driver that executes — there is exactly one place per host where a token is spelled, and the summary literally cannot show a flag the real link did not use. The recommended internal shape: a private `fn build_args(&self, req) -> Vec<String>` (or a small typed command struct) per impl that BOTH `link` (passes to `run_linker`) and `describe` (joins for display) consume. `describe` may elide absolute-path noise for readability, but every *token* it shows comes from `build_args`.

### 12.4 Intent → rendering table (the contract each impl satisfies)

Each row is one `LinkRequest` intent and how each driver renders it. The Apple/GNU columns are the live S80 behaviour relocated from §11.4; the MSVC column is a **sketch, not implemented** — present only to prove the trait does not preclude Windows (§12.7).

| Intent (`LinkRequest`) | `AppleLdLinker` (`ld`/ld64) | `GnuCcLinker` (`cc` driver) | `MsvcLinker` (sketch — not built) |
|---|---|---|---|
| `output` | `-o <out>` | `-o <out>` | `/OUT:<out>` |
| `startup_obj` + `module_objs` | listed first, as paths | listed first, as paths | listed as inputs |
| `entry_symbol` | `-e _<entry>` (Mach-O `_` prefix) | *(omit — crt's `_start` is default; the stub IS C `main`)* | `/ENTRY:<entry>` (or default crt) |
| `bundle_lib` | `-L<dir> -l<name>` | `-L<dir> -l<name>` | `<dir>\<name>.lib` |
| `force_include` (per archive) | `-force_load <rlib>` (raw rlib) | extract `.o` members (§12.5), then `-Wl,--whole-archive <obj…> -Wl,--no-whole-archive`, emitted **before** the bundle `-l` (§12.5 ordering) | `/WHOLEARCHIVE:<lib>` |
| `dead_strip == true` | `-dead_strip` | `-Wl,--gc-sections` *(currently omitted — optional for correctness, §11.4; impl may honour the flag or no-op it as today)* | `/OPT:REF` |
| *(host-implicit)* arch | `-arch arm64` | *(implicit from host `cc`)* | *(implicit from host `link.exe`)* |
| *(host-implicit)* platform/sdk | `-platform_version macos … …`, `-syslibroot $(xcrun …)` | *(none)* | *(none)* |
| *(host-implicit)* system libs | `-lSystem` | `-lpthread -ldl -lm` (driver adds `-lc`/`-lgcc_s`) | default CRT libs |
| invocation | `run_linker("ld", args)` | `run_linker("cc", args)` | `run_linker("link.exe", args)` |

Every cell in the Apple/GNU columns appears in **exactly one** impl. The caller and the diagnostic see none of them. This is the property D4 violated and §12 restores.

### 12.5 Where the GNU `.o`-extraction + link-order constraint live

Both are **internal to `GnuCcLinker`** — they are GNU-specific renderings of intents the request states platform-neutrally, so they have no home in the request and no analogue in the Apple impl:

- **`.o` extraction (`extract_rlib_objects`, `src/exe.rs:878`) is GNU's rendering of `force_include`.** A Rust `.rlib` is an `ar` archive carrying `lib.rmeta` (+ `lib.rmeta-link`) metadata members that GNU `ld`/mold reject under `--whole-archive` ("file format not recognized"); Apple `ld64` tolerates the raw rlib. So `AppleLdLinker` force-loads the raw `req.force_include[i].rlib` directly, while `GnuCcLinker` first extracts the object members (`ar t` → keep `*.o` → `ar x --output=<dir>`) and whole-archives only those. The extraction function moves *into* `GnuCcLinker` (a private method or a free fn in the GNU driver module) — it is dead code in any Apple build and meaningless to the caller. Its deterministic per-rlib cache dir (`<cache>/__plat_<stem>/`) derives from `req.startup_obj.parent()` exactly as today.

- **The link-order constraint is GNU's, and the GNU impl owns it.** GNU `ld` resolves a static archive only against symbols left undefined by inputs seen *so far*, so the whole-archived platform objects (which reference bundle symbols like `cranelisp_platform::adt::set_global_schema`) MUST be emitted **before** the bundle `-l`. `AppleLdLinker` (ld64) is order-insensitive here, so it has no such rule. Because each impl builds its own arg vector, the GNU impl simply places the `--whole-archive` group before the bundle `-l` in *its* `build_args`; the Apple impl orders to its own taste. The ordering is no longer a comment a maintainer must remember across two parallel functions — it is local to the one impl that needs it.

The abstraction **cleanly houses both**: they are exactly the kind of platform-private rendering detail that the parallel-driver structure scattered and the trait structure confines. The request says "force-include these archives"; how GNU makes that survive its linker (extract, whole-archive, order-before-bundle) is the GNU impl's business and nobody else's.

### 12.6 Selection mechanism + where it lives

**Selection keeps the existing `cfg`-based host dispatch**, lightly reshaped: `for_host()` returns the chosen `Linker` rather than a config struct.

```rust
/// The native linker driver for the current host (replaces LinkerConfig::for_host).
fn for_host() -> Result<Box<dyn Linker>, CranelispError> {
    match (cfg!(target_arch = "aarch64"), std::env::consts::OS) {
        (true, "macos") => Ok(Box::new(AppleLdLinker::new())),
        (true, "linux") => Ok(Box::new(GnuCcLinker::new())),
        _ => Err(/* the existing "only supported on aarch64 macOS and aarch64 Linux" error */),
    }
}
```

**`Box<dyn Linker>` over an enum-dispatch — justified.** There are exactly two live impls and dispatch happens once per `--link` (not in a hot loop), so the virtual-call cost is irrelevant; the `Box<dyn>` form keeps each impl's surface (its private `build_args`, its Apple-only `get_sdk_sysroot`, its GNU-only `extract_rlib_objects`) fully encapsulated in its own type with no shared enum forced to carry both platforms' fields — which is precisely the leak §11.6's flat `LinkerConfig` (macOS fields `Option`-nulled on Linux) embodied. The trait-object form makes "a token lives in exactly one impl" the default; an enum with a `match self` in every method re-opens the door to a shared body touching both platforms' tokens. (If a future need for `const`/no-alloc selection arises, an enum wrapper delegating to the same impls is a mechanical change — but it is not warranted now.)

**Where it lives: int-internal, `src/exe.rs` (or a new `src/link/` submodule — recommended).** Per §8, `link_executable` and its driver functions are in the **binary crate (`src/`), `/int`-owned**; `/backend` owns this *design* + the Cranelift startup-stub, not the linker-invocation source. The abstraction stays entirely within the binary crate:

- **No `cranelisp-types` change.** `LinkRequest`, `BundleLib`, `ForceIncludeArchive`, `Linker`, and the impls are int-internal types. None crosses a crate boundary (the only cross-crate type already in play is `cranelisp_backend::exe::PlatformLayoutCheck`, consumed by `generate_startup_object` — untouched by this refactor).
- **No public-API impact.** The binary crate has no `public-api.txt` baseline (it is the application, not a library surface); `link_executable` is `pub` only within `src/` for `session_v4.rs` to call. The refactor may keep `link_executable(req: &LinkRequest)` as the one `pub(crate)` entry (it builds `for_host()` and calls `.link(req)`), or expose `for_host()` — either way no library crate's surface moves, so **no baseline regeneration and no facade edit** (`facades/int.md` describes the int *library* surface, not these internal link helpers).

**Recommendation: a new `src/link/` module** (`src/link/mod.rs` with `request.rs`, `apple.rs`, `gnu.rs`). `src/exe.rs` is already large (~1150 lines mixing startup-stub emission, main-validation, bundle/rlib location, and linking); extracting the linker drivers into `src/link/` gives each impl its own file — the structural counterpart to "each token lives in one place." `src/exe.rs` retains startup-stub/alias generation, `main` validation, and the bundle/rlib *locators* (`find_bundle_lib`, `find_platform_rlibs`), and calls into `src/link/`. This is a `/dev` call; `src/exe.rs`-internal is also acceptable. Either way the module boundary is below the crate edge — no surface implications.

### 12.7 The MSVC shape (not implemented — the trait must not preclude it)

Windows is out of scope (§1 non-goals), but the trait is designed so a `MsvcLinker` could be added by writing one impl and one `for_host()` arm, with **zero change to `LinkRequest` or the caller**. The MSVC column of §12.4 sketches the renderings: `/OUT:`, `/ENTRY:` (or crt default), `<name>.lib`, `/WHOLEARCHIVE:<lib>` (MSVC's native force-include — it takes the archive directly, so MSVC would *not* need the GNU `.o`-extraction dance, confirming extraction is correctly a GNU-private detail and not a request-level concern), `/OPT:REF` for dead-strip, `link.exe` as the driver. The fact that MSVC's force-include is a single flag over the raw `.lib` — neither the Apple `-force_load` nor the GNU extract-and-whole-archive — is the proof that `force_include` is correctly modelled as *intent*: three toolchains render it three different ways, and only the request's platform-neutral "make these survive" is common. No field of `LinkRequest` is Apple- or GNU- or MSVC-shaped.

### 12.8 `/dev` migration map (precise — which current code moves where)

The refactor is a structure-preserving relocation; no link behaviour changes on either live platform (that is the acceptance bar — the ~13 D4 reds go green because the Linux path stops emitting `-force_load`, and the macOS/GNU happy paths stay byte-identical in the commands they issue).

| Current code (`src/exe.rs`) | Moves to | Notes |
|---|---|---|
| `enum LinkDriver` (`:600`) | **deleted** | Subsumed by the `Box<dyn Linker>` selection; the variant identity is now the impl type. |
| `struct LinkerConfig` + fields (`:612`) | **deleted** (fields redistributed) | `stub_entry_symbol`/`user_main_symbol` were already read via `host_entry_symbols()` (keep that fn — it stays the source of the stub/alias names, and now also feeds `req.entry_symbol`); `arch`/`platform_triplet` become `AppleLdLinker` internal constants. |
| `LinkerConfig::for_host()` (`:629`) | `for_host() -> Box<dyn Linker>` | Same `cfg` match; returns the impl instead of the config. |
| `host_entry_symbols()` (`:660`) | **unchanged** | Still computes `(stub_entry_symbol, user_main_symbol)` for `session_v4.rs`'s stub/alias emission; the caller now also passes `stub_entry_symbol` into `req.entry_symbol`. |
| `link_executable(...)` dispatch (`:671`) | thin entry: build `LinkRequest`, `for_host()?.link(&req)` | The caller in `session_v4.rs:4121` either keeps calling `link_executable` (which now composes the request) OR `session_v4.rs` composes `LinkRequest` and calls `for_host()?.link()` directly — `/dev`'s call. The bundle dir/name derivation (`:680`–`:688`) becomes `BundleLib { dir, name }` construction. |
| `link_executable_apple_ld(...)` (`:723`) | `AppleLdLinker::link` (+ private `build_args`) | Body relocated verbatim; reads `arch`/triplet from impl constants instead of `config`; `get_sdk_sysroot()` becomes an Apple-impl-internal call. The `-force_load <rlib>` loop renders `req.force_include`. |
| `link_executable_cc(...)` (`:793`) | `GnuCcLinker::link` (+ private `build_args`) | Body relocated; the `--whole-archive` group renders `req.force_include`, calling the now-internal `extract_rlib_objects`; preserves the before-bundle ordering. |
| `extract_rlib_objects(...)` (`:878`) | `GnuCcLinker` private (method or module-private fn) | GNU-only; extraction root from `req.startup_obj.parent()`. |
| `run_linker(...)` (`:977`) | shared helper (stays in `src/exe.rs` or `src/link/`) | Both impls call it; no change. |
| `get_sdk_sysroot()` (`:999`) | `AppleLdLinker` private | Apple-only; only `AppleLdLinker::link` calls it (the `_ => Err` host arm of the old `for_host` never reached it anyway). |
| **`log_link_summary(...)` (`:1025`)** | **DELETED → `Linker::describe`** | **The D4 fix.** The hardcoded `-force_load` (`:1054`) is gone. `link_executable` (or the call site) prints `linker.describe(&req)` — each impl renders the real command it will run, from its own `build_args`. The `; Linking: …` line now shows GNU tokens on Linux and Apple tokens on macOS, always matching the executed command. |
| `find_bundle_lib` / `find_platform_rlibs` / `resolve_platform_rlib` (`:1091`+) | **unchanged** | These are *locators* (produce the paths the request carries), not drivers. They stay in `src/exe.rs`. `find_platform_rlibs` output becomes `req.force_include` (`Vec<ForceIncludeArchive>`). |

**`describe` must be called for the diagnostic, and the hardcoded `-force_load` must be deleted** — these are the same instruction stated two ways, and it is the load-bearing line of the migration. Any path that still spells `-force_load` outside `AppleLdLinker` is the D4 bug surviving the refactor.

**Acceptance (for the `/dev` → `/review` cycle):** warm full-workspace build (the §11.5 build-skew caveat — verify only after one `cargo build --workspace`); the ~13 `output_equivalence` link permutations + `platform_stdio_print_link` go GREEN on Linux; `roundtrip_link` / `hash_gate_link_refuses` stay green; the macOS link command is byte-identical to pre-refactor (no token added or dropped); `grep -rn 'force_load' src/` returns hits only inside the `AppleLdLinker` impl.

### 12.9 No public-API impact — confirmation

Confirmed against the canonical set: this change is **int-internal** with **no cross-crate surface movement**.
- **No `cranelisp-types` edit** — no boundary DTO or trait changes; `LinkRequest`/`Linker` are binary-crate types.
- **No library facade edit** — `facades/int.md` describes int's *library* surface (`src/lib.rs`), not the `--link` orchestration internals; `link_executable` and the new types are `pub(crate)`/binary-internal.
- **No `public-api.txt` regeneration** — the binary crate has no tracked baseline; no library crate's `public-api.txt` is touched.
- **No `bounded-contexts.md` / sequence-diagram edit** — BC §6 (int) already owns "`--link` standalone executable generation"; the linker-driver internal restructure does not change any cross-crate call shape or flow depicted in `sequences/exec-flow-link.*`. The `session_v4.rs → exe::link_executable` arrow is preserved (the function may keep its name; if `/dev` routes the caller to `for_host()?.link()` directly, the arrow's target rename is below the facade granularity the diagram tracks — no signature crossing a crate edge changes).

This section (and §11) is the manifestation site for the abstraction (a backend-owned subsystem design doc per §8 — the `--link` design home); the canonical-set audit sweep finds no consequent edit owed elsewhere.
