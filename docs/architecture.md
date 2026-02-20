# Architecture

## Pipeline Overview

Cranelisp processes source code through a linear pipeline:

```
Source text
    |
    v
[Sexp Reader]           sexp.rs — S-expression reader, produces Sexp tree
    |
    v
Sexp
    |
    v
[Macro Expander]        macro_expand.rs — defmacro compilation + sexp expansion
    |
    v
Expanded Sexp
    |
    v
[AST Builder]           ast_builder.rs — Sexp -> AST conversion
    |
    v
AST                     ast.rs — Expr, TopLevel, TraitDecl, TraitImpl, DefnMulti, Span
    |
    v
[Type Checker]          typechecker.rs — Algorithm W, Hindley-Milner inference,
    |                       trait registry, method resolution, constrained polymorphism
    v
Typed environment       types.rs — Type, Scheme (with constraints), substitution map
+ MethodResolutions     maps AST spans to resolved trait/overload/curry calls
    |
    v
[Codegen]               codegen.rs — AST -> Cranelift IR translation
    |                       (see docs/backend-selection.md for backend abstraction)
    v
Cranelift IR
    |
    v
[JIT]                   jit.rs — JITModule finalize, symbol registration, execution
    |
    v
Execute main()
```

Note: `parser.rs` is the legacy single-pass PEG path that produces identical ASTs. The two-phase path (`sexp.rs` → macro expansion → `ast_builder.rs`) is the primary pipeline.

## Module Responsibilities

- **`main.rs`**: Entry point. Parses `--run`, `--exe`, and `--cwd` flags. `cranelisp` launches the bare REPL, `cranelisp foo.cl` opens the REPL with the file's module graph loaded, `cranelisp --run foo.cl` runs in batch mode (compile + call main + exit), `cranelisp --run` runs `user.cl` from CWD in batch mode, `cranelisp --exe <output> [file.cl]` exports a standalone native executable.
- **`error.rs`**: Single `CranelispError` enum covering parse, type, and codegen errors. All variants carry source spans.
- **`ast.rs`**: Data types for the abstract syntax tree. `TopLevel::Defn` for function definitions, `TopLevel::DefnMulti` for multi-signature functions, `TopLevel::TraitDecl` and `TopLevel::TraitImpl` for traits. `Expr` for expressions.
- **`sexp.rs`**: S-expression reader. Converts source text into `Sexp` trees (`Symbol`, `Int`, `Float`, `Bool`, `Str`, `List`, `Bracket`). Phase 0 of the macro expansion pipeline.
- **`ast_builder.rs`**: Converts `Sexp` trees into the same AST types as the PEG parser (`Expr`, `TopLevel`, `ReplInput`). Phase 1 of the macro expansion pipeline. Handles special form dispatch, type annotation processing, and `bind!`/`list` desugaring.
- **`parser.rs`**: Legacy single-pass PEG grammar using the `peg` crate. Produces identical ASTs to the `sexp.rs` → `ast_builder.rs` path.
- **`types.rs`**: Type representation (`Int`, `Bool`, `String`, `Float`, `Fn`, `Var`, `ADT`) and type schemes with constraints for polymorphism. `IO` is represented as `ADT("IO", [a])` — a compiler-seeded ADT, not a separate type variant.
- **`typechecker.rs`**: Implements Algorithm W. Two-pass: first register all function signatures with fresh type variables, then check each body. Trait registry and method resolution via `MethodResolutions`. Constrained polymorphism detection and monomorphisation. Arithmetic operators (`+`, `-`, `*`, `/`) and comparisons (`=`, `<`, `>`, `<=`, `>=`) are dispatched through the trait system (Num, Eq, Ord). Name resolution uses module-walk through `CompiledModule` symbol tables (`lookup` → `lookup_via_modules` → `resolve_in_module`).
- **`captures.rs`**: Free variable analysis for closures. Computes which variables a lambda captures.
- **`codegen.rs`**: Translates typed AST to Cranelift IR. Each expression variant maps to specific Cranelift instructions. Handles closure allocation, the env_ptr calling convention, inline primitives for operators, and auto-curry wrapper generation.
- **`jit.rs`**: Manages the `JITModule` lifecycle. Two constructors: `Jit::new()` for the built-in stdio platform (default), `Jit::with_platform(path)` for dynamically-loaded platform DLLs via `libloading`. Holds `loaded_library: Option<Library>` (declared before `module` for correct drop order). Shared initialization logic factored into helper functions (`build_isa`, `register_non_platform_symbols`, `declare_non_platform_functions`, `declare_platform_functions_static`, `declare_platform_functions_owned`). Handles function pointer tables (`fn_table` for REPL, `module_gots` for multi-module batch), builtin symbol registration, and code compilation/execution methods. All per-function metadata (source, sexp, defn, CLIF IR, disasm, code_size, compile_duration, got_slot, code_ptr, param_count) is owned by `CompiledModule`. `build_fn_slots_from_modules()` builds the fn_slots map from `CompiledModule` data. `populate_builtin_func_ids()` backfills `FuncId`s onto `DefKind::Primitive` module entries after JIT initialization. Provides save/restore methods for module GOT entries to support rollback on failed module reloads. See `docs/backend-selection.md` for the design to abstract this behind a `Backend` trait.
- **`display.rs`**: Type display formatting. Renders types in cranelisp notation with trait constraints (e.g. `:Num a =>`).
- **`module.rs`**: Module graph: `(mod)` discovery, `(import)/(export)` parsing, dependency graph, topological sort, unified module resolution (`resolve_module` for submodule→root→lib search, `resolve_root_module` for root/lib-only), implicit prelude import injection, lib directory fallback. Defines `CompiledModule` and `ModuleEntry` types — per-module symbol tables that own definitions, imports, re-exports, type definitions, constructors, macros, and codegen artifacts. `DefKind` enum (`SpecialForm`, `Primitive`, `UserFn`) and `DefCodegen` struct narrow the `ModuleEntry::Def` variant. `DefKind::Primitive` carries `jit_name: Option<JitSymbol>` and `func_id: Option<FuncId>` for resolution-based dispatch. Synthetic modules (`primitives`, `platform.stdio`) are registered by the Rust runtime; `is_synthetic_module()` supports `platform.*` namespace for additional platform modules. See `docs/modules.md` and `docs/name-resolution.md`.
- **`platform.rs`**: Platform loading infrastructure. Re-exports C-ABI contract types (`PlatformFnC`, `HostCallbacksC`, `PlatformManifestC`), `OwnedPlatformFnDescriptor`, and `manifest_to_descriptors()` from the `cranelisp-platform` shared crate. Contains `resolve_platform_path()` for searching `./platforms/` and `~/.cranelisp/platforms/`.
- **`cache.rs`**: Compiled module cache system. Manages the `.cranelisp-cache/` directory, source hashing (SHA-256), manifest read/write, `CompiledModule` serialization/deserialization, and `compile_module_to_object()` which re-compiles function definitions into a relocatable `.o` file using `cranelift-object` `ObjectModule` with PIC mode. Called from `batch.rs` after each module compiles.
- **`linker.rs`**: Minimal linker for loading cached `.o` files. Parses Mach-O and ELF object files (via the `object` crate), allocates executable memory (`mmap` + `mprotect`), resolves aarch64 relocations (branch, page, page-offset, GOT-load, absolute) against registered symbols, and manages a linker-internal GOT for PIC data references. Integrated into the batch load path: cached modules are loaded via the `Linker` instead of recompiling. The `Linker` must outlive execution since it owns `mmap`'d code regions.
- **`intrinsics.rs`**: Language-internal `extern "C"` implementations (`alloc` for closure and string heap allocation). Not visible to user code.
- **`primitives/`**: Pure bootstrap functions in Rust, organized per-type (`int.rs`, `bool.rs`, `string.rs`, `float.rs`). Registered under the `primitives` synthetic module. Operator wrapper functions for first-class operator values. Includes `parse-int` (String -> Option Int) for type-safe integer parsing.

## Workspace Crates

The project is a Cargo workspace with multiple members:

- **`cranelisp`** (root) — the compiler/REPL binary
- **`cranelisp-runtime/`** — rlib crate containing all `extern "C"` runtime functions (intrinsics, primitives, marshal). Extracted from the main crate so the exe pipeline can bundle them into a staticlib.
- **`cranelisp-platform/`** — shared interface crate defining the C-ABI contract between host and platform DLLs (`PlatformFn`, `HostCallbacks`, `PlatformManifest`, `ABI_VERSION`, `declare_platform!` macro, `manifest_to_descriptors()`, `OwnedPlatformFnDescriptor`). Provides safe wrapper types (`CLInt`, `CLString`, `CLBool`, `CLFloat`) with `#[repr(transparent)]` over `i64` — platform authors use `From`/`Into` conversions and `CLString::as_str()` instead of raw pointer arithmetic. `HostContext` stores global allocator; `declare_platform!` macro generates the manifest entry point from declarative metadata.
- **`cranelisp-exe-bundle/`** — staticlib crate that re-exports `cranelisp-runtime` and platform crates. Linked into standalone executables to provide runtime functions. Using a single staticlib avoids duplicate Rust std symbols.
- **`platforms/stdio/`** — reference stdio platform DLL (cdylib + rlib). Implements `print` and `read-line` using `CLString`/`CLInt` wrapper types and the `declare_platform!` macro.
- **`platforms/test-capture/`** — test harness platform DLL (cdylib). Captures print output to in-memory buffers and returns scripted input from `read-line` using `CLString`/`CLInt` wrapper types. Exports test utilities (`test_capture_set_input`, `test_capture_get_output`, `test_capture_reset`) for Rust integration tests.

## Compilation Phases (Two-Pass)

1. **Declare**: Register all function signatures with the Cranelift module. Each function gets fresh type variables.
2. **Define**: Compile each function body to Cranelift IR, using the declared signatures for calls.

This two-pass approach enables forward references and mutual recursion without requiring declaration ordering.

## Data Flow

```
Program = Vec<TopLevel>
TopLevel = Defn { name, params, body, span }
         | DefnMulti { name, variants, span }
         | TraitDecl { name, methods, span }
         | TraitImpl { trait_name, target_type, methods, span }
         | TypeDef { name, type_params, constructors, span }

Expr = IntLit | BoolLit | FloatLit | StringLit
     | Var | Let | If | Lambda | Apply
     | Match
     (each variant carries a Span)

Note: `do`, `bind!`, `list`, `vec` are prelude macros. `pure` and `bind` are library functions in `lib/core/io.cl`. `IO` is a compiler-seeded ADT.
```

## File Watching and Module Hot-Reload

The REPL watches loaded `.cl` files for external changes (via the `notify` crate) and incrementally reloads affected modules.

### Architecture

- **`repl/watch.rs`**: `FileWatcher` wraps `notify::RecommendedWatcher`. Watches parent directories of module files (reliable across editors that use atomic rename). Self-write suppression prevents the REPL's own save-to-file from triggering reloads.
- **Polling**: At the top of the REPL loop (before prompting, only when the input buffer is empty), `poll_changes()` drains the event channel non-blocking.
- **Reload**: `reload_module()` implements a four-phase protocol:
  - **Phase A (Save)**: Remove old `CompiledModule`, save GOT entries and JIT defs for rollback, remove macros
  - **Phase B (Recompile)**: Rebuild `ModuleGraph` from the file, call `compile_module_graph` (skips already-loaded dependencies)
  - **Phase C (Validate)**: Compare exported public symbol schemes between old and new modules. Schema comparison uses display-string equality (pragmatic for v1)
  - **Phase D (Commit or Rollback)**: On success with compatible types, refresh type defs. On failure or type incompatibility, restore old `CompiledModule`, write old code pointers back to GOT slots, restore JIT defs
- **Locked modules**: Failed reloads lock the module — definitions are rejected, save-to-file is blocked, but expressions still evaluate against the restored GOT code. File changes trigger retry; `/reload` retries manually.

### Key Design Decisions

1. **GOT-based indirection**: All cross-module calls go through per-module GOTs. Rewriting GOT slots atomically redirects all callers to new code.
2. **Old code not freed**: JIT-compiled code is never deallocated, so old code pointers remain valid after reload. This enables safe rollback.
3. **Single-module scope**: Only the changed module is recompiled. Dependent modules are not recompiled — if a type signature changes incompatibly, the reload is rejected rather than cascading.
4. **Self-write suppression**: The save-to-file mechanism (triggered by REPL definitions) pre-registers the file path with the watcher to skip the next event for that path. A 2-second timeout clears stale suppressions.

## Compiled Module Cache

Cranelisp can persist compiled module artifacts to disk to enable future reuse. The cache system lives in `cache.rs` (serialization, hashing, ObjectModule compilation) and `linker.rs` (loading `.o` files and resolving relocations).

### Cache Layout

The cache uses a two-tier directory structure. **Lib modules** (those whose source lives under the lib directory) cache alongside the lib sources, so all projects sharing the same lib directory share the same cached core/prelude. **Project modules** cache locally in the project directory.

```
{lib_dir}/.cranelisp-cache/       # shared lib cache (core, prelude)
  manifest.json
  core.meta.json / core.o
  prelude.meta.json / prelude.o

{project_root}/.cranelisp-cache/  # project-local cache
  manifest.json
  <module>.meta.json / <module>.o
```

Each tier has its own `manifest.json` tracking only its own modules. Module names are sanitized for the filesystem: dots become underscores, the root module uses `_root`. Both `.cranelisp-cache/` directories are gitignored.

### Write Path (batch mode)

Cache writes happen in `batch.rs` `run_project()` after each module compiles:

1. **Accumulate**: As each function is compiled to JIT code, the `Defn`, `Scheme`, `MethodResolutions`, and `expr_types` are accumulated into per-module vectors.
2. **Serialize metadata**: The `CompiledModule` is serialized to `<module>.meta.json` via serde.
3. **Compile to object**: `compile_module_to_object()` in `cache.rs` creates a `cranelift-object` `ObjectModule` (with PIC mode enabled) and re-compiles each function definition using the same `compile_function_indirect<M: Module>()` codegen path. GOT references become `DataSymbol` entries (imported data symbols resolved at link time) instead of `Immediate` constants. Intrinsics, builtins, and platform functions are declared as imported functions.
4. **Write `.o`**: The ObjectModule product is emitted as a relocatable object file.
5. **Update manifest**: `manifest.json` records the SHA-256 source hash for each module.

All cache writes are best-effort — failures produce warnings but do not abort compilation.

### Cache Invalidation

Each module's source text is hashed with SHA-256. The manifest records the hash alongside the cranelisp version and target triple. A cached module is valid only when:

- The cranelisp binary version matches exactly
- The target architecture and OS match
- The source hash matches the current file contents

### ObjectModule Compilation

`compile_function_indirect` is generic over `M: Module`, supporting both `JITModule` (runtime) and `ObjectModule` (cache). The key difference is GOT base address resolution:

- **JITModule**: `GotReference::Immediate(i64)` — the GOT base is a known address, embedded as an `iconst` instruction.
- **ObjectModule**: `GotReference::DataSymbol(DataId)` — the GOT base is an imported data symbol (`__cranelisp_got_<module>`), resolved via relocation at load time.

### Load Path (batch mode)

On subsequent batch runs, `batch.rs` `run_project()` checks the cache before compiling each module:

1. **Per-module cache check**: The manifest's SHA-256 source hash for the module is compared against the current file contents. If the hash matches (and the cranelisp version and target triple match), the cached artifacts are used instead of recompiling.
2. **Cached module restoration**: The `CompiledModule` is deserialized from `<module>.meta.json` and installed into the `TypeChecker`'s module table. This restores all symbol tables, type schemes, method resolutions, and codegen metadata.
3. **Macro reconstruction**: Macros stored in the cached `CompiledModule` include their original `Sexp` source. These are recompiled from the stored Sexp to reconstruct live function pointers in the `MacroEnv`, since function pointers cannot be serialized.
4. **Object loading**: The `<module>.o` file is loaded via the `Linker` (see below), which `mmap`s the object into executable memory and resolves all relocations.
5. **GOT population**: The linker-resolved code pointers for each function are written into the per-module GOT slots, matching the same layout as freshly JIT-compiled code.

Cache hits skip the entire pipeline (parsing, macro expansion, AST building, type checking, Cranelift compilation) for that module.

### Linker

`linker.rs` provides a minimal linker for loading cached `.o` files back into executable memory. It handles:

- Parsing Mach-O and ELF object files (via the `object` crate)
- Allocating executable memory regions (`mmap` + `mprotect`)
- Resolving relocations against registered symbols (intrinsics, builtins, platform DLLs, GOT bases)
- Mach-O aarch64 relocations: `BRANCH26`, `PAGE21`, `PAGEOFF12`, `GOT_LOAD_PAGE21`, `GOT_LOAD_PAGEOFF12`, `UNSIGNED`
- ELF aarch64 relocations: `CALL26`, `ADR_PREL_PG_HI21`, `ADD_ABS_LO12_NC`, `LDST64_ABS_LO12_NC`, `ABS64`
- Mach-O leading underscore stripping for cross-format symbol compatibility
- **Linker-internal GOT**: `GOT_LOAD_PAGE21`/`GOT_LOAD_PAGEOFF12` relocations (used by PIC code for data symbol references) are resolved through a linker-managed GOT region, `mmap`-allocated near the code segment to stay within the ADRP ±4GB addressing range

The `Linker` instance must outlive program execution because it owns the `mmap`'d code regions. If the `Linker` is dropped, the executable memory is unmapped and function pointers become dangling.

### Limitations

- **No REPL caching**: Only batch mode (`--run`) reads and writes cache files. The REPL does not use cached modules.
- **Constrained fn specializations not cached**: Monomorphised specializations of constrained polymorphic functions are compiled on-demand and not included in the `.o` file.
- **Stale cache compatibility**: Cache files produced by a different version of cranelisp are not automatically detected beyond the version string in the manifest. Incompatible internal format changes can cause test failures or incorrect behavior; users should clear both `.cranelisp-cache/` directories (project-local and `lib/.cranelisp-cache/`) when upgrading.

## Standalone Executable Generation

Cranelisp can produce native macOS aarch64 executables via `--exe <output>` (CLI) or `/exe` (REPL). The exe pipeline links cached module `.o` files with runtime functions into a standalone binary.

### Pipeline

```
Module .o files (from cache)
    +
Startup stub .o (generated)      exe.rs — generate_startup_object()
    +
Runtime bundle .a (staticlib)    cranelisp-exe-bundle crate
    |
    v
[System linker]                  ld -arch arm64 -e _start
    |
    v
Native executable
```

### Components

- **`exe.rs`**: Generates the startup stub (`_start` initializes platforms, calls `main()`, converts result to exit code via `exit()`), compiles monomorphised specializations to `.o`, and invokes the system linker.
- **`cranelisp-exe-bundle/`**: Staticlib crate that bundles `cranelisp-runtime` and platform crates. Provides `cranelisp_init_platform()` for startup-time platform initialization (constructs `HostCallbacks` and calls the platform's manifest function).
- **`batch.rs` `build_executable()`**: Orchestrates the pipeline — runs `compile_project_pipeline()` (which writes `.o` cache files without executing `main`), collects `.o` paths, generates the startup and mono stubs, locates the bundle `.a`, and calls `link_executable()`.

### Startup Stub

The startup stub is a minimal Cranelift-generated object file containing a single exported function `_start`:
1. For each platform, calls `cranelisp_init_platform(func_addr(cranelisp_platform_manifest))` — this initializes `HostContext` and sets `GLOBAL_ALLOC` so platform functions can allocate strings and IO values
2. Calls `main()` (imported from the entry module's `.o`)
3. Narrows the i64 return value to i32 via `ireduce`
4. Calls `exit()` (imported from libc via the system linker)

### Linker Invocation

```
ld -arch arm64 -o <output> -e _start \
  <startup.o> <module1.o> ... <moduleN.o> <mono.o> \
  -L<target/debug> -lcranelisp_exe_bundle \
  -platform_version macos 14.0 14.0 \
  -lSystem -syslibroot <SDK path>
```

### GOT Data Sections

Each module's `.o` file exports its GOT as an initialized data section (`__DATA,__data`), with function-address relocations that the system linker resolves. This enables cross-module calls via GOT indirection in the linked executable, matching the JIT runtime's GOT-based calling convention.

### CLI Usage

```sh
cranelisp --exe hello examples/hello.cl   # build executable
./hello                                     # run it
```

### REPL Usage

```
user> /exe hello     ; export current session as executable
user> /exe           ; uses current module name as output
```

All values are `i64` at runtime:
- `Bool` is `0`/`1` in an `i64`
- `String` is a heap pointer to `[i64 len][u8 bytes...]`
- `Float` stores IEEE 754 f64 bits via bitcast to i64
- `IO a` is a real ADT: `(deftype (IO a) (IOVal [:a ioval]))` — data constructors are heap `[tag, fields...]` like other ADTs
- ADT values: nullary constructors are bare i64 tags (0, 1, ...), data constructors are heap pointers to `[i64 tag, fields...]`
- `Fn` values are pointers to heap-allocated closure structs (see `docs/closures.md`)
