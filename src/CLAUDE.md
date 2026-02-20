# Cranelisp — Project Conventions

## Overview
Cranelisp is a statically typed, pure functional Lisp that JIT compiles via Cranelift.
Inspired by Carp (typed Lisp, no GC) and Clojure (syntax, pure functional).

## Pipeline
```
Source text -> [Sexp Reader] -> Sexp -> [Macro Expander] -> Sexp -> [AST Builder] -> AST -> [Type Checker] -> typed env + method resolutions -> [Codegen] -> Cranelift IR -> [JIT] -> execute main()
```

## Module Map
| File | Responsibility |
|---|---|
| `main.rs` | Entry point: parses `--run`/`--cwd` flags. `cranelisp` = bare REPL, `cranelisp foo.cl` = REPL with file, `cranelisp --run foo.cl` = batch, `cranelisp --run` = batch user.cl |
| `lib.rs` | Re-exports all modules |
| `batch.rs` | Batch-mode pipeline: parse, typecheck, compile, run. Deferred per-module cache writes (`.meta.json`, `.o`, `manifest.json`) to `.cranelisp-cache/` after entire compile loop completes (mono specializations may land in earlier modules). Exports `try_load_cached_module()` shared by batch and REPL |
| `repl/` | Interactive REPL (submodules: `mod.rs` `ReplSession` struct + `run()`/`run_with_file()`/`run_repl_loop()` + `project_root` field + prelude loading + module graph compilation + cache read/write via `compile_module_graph`, `commands.rs` slash command enum + parser, `handlers.rs` `/sig` `/doc` `/type` `/info` and other command handlers, `input.rs` per-`ReplInput` variant handlers, `format.rs` type/value/symbol/signature formatting + special form docstrings, `util.rs` string reading + paren balancing) |
| `ast.rs` | `Expr`, `TopLevel`, `TraitDecl`, `TraitImpl`, `Span` types. AST nodes carry optional docstrings. `desugar_type_def()` shared transform |
| `sexp.rs` | S-expression reader: source text → `Sexp` tree (Phase 0 of macro pipeline) |
| `ast_builder.rs` | `Sexp` → AST builder: converts `Sexp` trees into `Expr`/`TopLevel`/`ReplInput` (Phase 1 of macro pipeline) |
| `macro_expand.rs` | `defmacro` compilation and S-expression expansion (Phase 4 of macro pipeline). `MacroEnv` stores compiled macros, `expand_sexp` recursively expands macro calls |
| `types.rs` | `Type`, `Scheme`, `TypeId` |
| `typechecker/` | Algorithm W (Hindley-Milner) type inference, trait registry, method resolution. Two-layer name resolution: `local_env` (params/let/match) → module-walk (`resolve_in_module` via `CompiledModule`). `SymbolMeta` enum (SpecialForm/Primitive/UserFn) stores docstrings + param names; `TypeDefInfo`/`ConstructorInfo` store per-type/per-constructor docstrings |
| `codegen/` | AST -> Cranelift IR translation (submodules: `mod.rs` types/entry points, `expr.rs` expression compiler, `apply.rs` function application, `closures.rs` lambda/closure wrappers, `match_compile.rs` pattern matching, `primitives.rs` inline primitive IR) |
| `jit.rs` | `JITModule` lifecycle, builtin registration, execution |
| `marshal.rs` | Marshalling between Rust `Sexp` and JIT-runtime Sexp ADT values |
| `captures.rs` | Free variable analysis for closures |
| `display.rs` | Type display formatting with trait constraints (`:Num a =>`) |
| `unittest_prelude.cl` | Test fixture for unit tests: types, traits, impls, functions — no macros/Sexp. Each test module `include_str!`s it directly |
| `names.rs` | Name newtypes: `Symbol`, `ModuleFullPath`, `FQSymbol` (module + symbol pair). Utility functions: `split_qualified`, `split_dotted`, `parse_name`, `resolve_bare_name` |
| `module.rs` | Module graph: `(mod)` discovery, `(import)/(export)` parsing, dependency graph, topological sort, unified module resolution (`resolve_module`/`resolve_root_module`), implicit prelude import injection, lib directory fallback. Also defines `CompiledModule` + `ModuleEntry` types for per-module symbol tables. `CompiledModule` has transient cache fields (`cache_method_resolutions`, `cache_expr_types`) for `.o` emission |
| `intrinsics.rs` | Language-internal `extern "C"` implementations (`alloc`, `panic`) |
| `platform.rs` | Platform loading infrastructure. Re-exports C-ABI contract types from `cranelisp-platform` shared crate (`PlatformFnC`, `HostCallbacksC`, `PlatformManifestC`, `OwnedPlatformFnDescriptor`, `manifest_to_descriptors()`), path resolution (`resolve_platform_path`) |
| `primitives/` | Pure bootstrap functions in Rust (per-type modules: `int.rs`, `bool.rs`, `string.rs`, `float.rs`). Includes `parse-int` (String -> Option Int) |
| `cache.rs` | Compiled module cache: SHA-256 source hashing, `.cranelisp-cache/` directory management, `CompiledModule` serialization, `compile_module_to_object()` for ObjectModule `.o` emission, cache manifest read/write, `write_module_cache()` shared helper for batch and REPL, atomic file writes |
| `linker.rs` | Minimal linker for cached `.o` files: `object` crate parsing, `mmap`+`mprotect` executable regions, Mach-O aarch64 and ELF aarch64 relocation resolution, symbol registration and lookup |
| `error.rs` | `CranelispError` enum with spans |

## Key Patterns
- **Parser**: Two-phase — `sexp.rs` reads S-expressions, `ast_builder.rs` builds AST
- **Type Checker**: Algorithm W with mutable substitution map, two-pass (declare all sigs, then check bodies)
- **Traits**: `deftrait`/`impl` with static dispatch via method resolution (mangled names like `show$Int`)
- **Builtins**: `extern "C"` fns registered via `JITBuilder::symbol()`
- **All types -> i64 at runtime**: Bool is 0/1 in i64, String is heap pointer to `[i64 len][u8 bytes...]`, Float stores f64 bits via bitcast, ADT nullary ctors are bare i64 tags, data ctors are heap `[tag, fields...]`
- **IO as ADT**: `IO` is a compiler-seeded ADT `(deftype (IO a) (IOVal [:a ioval]))` in the `primitives` module. `pure` and `bind` are library functions in `lib/core/io.cl`. `do` and `bind!` are prelude macros in `lib/core/syntax.cl`
- **Prelude macros**: `list`, `do`, `bind!`, `vec` are `defmacro`s in the prelude (not parser sugar). `list` expands to nested `Cons`/`Nil`, `bind!` expands to nested `bind`/`fn`, `do` expands to nested `let [_ ...]`

## Build / Test / Run
```sh
just build              # cargo build
just test               # cargo test
just run examples/hello.cl  # batch mode (--run)
just hello              # shortcut
just factorial           # shortcut
```

## Coding Conventions
- Rust 2024 edition
- No `unwrap()` in the pipeline — use `CranelispError` with spans
- Spans on all AST nodes for error reporting
- `extern "C"` calling convention for all compiled functions and builtins
