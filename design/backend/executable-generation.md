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
