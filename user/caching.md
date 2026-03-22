# Module Caching

Cranelisp automatically caches compiled modules so that unchanged code does not need to be recompiled. This speeds up builds for projects with multiple modules -- the standard library, shared utilities, and other stable dependencies are compiled once and reused on subsequent runs.

## How It Works

When you run a batch program with `--run`, Cranelisp creates a `.cranelisp-cache/` directory in your project root. This directory stores compiled object files and metadata for each module. On the next run, any module whose source has not changed is loaded directly from the cache, skipping the full compilation pipeline.

You do not need to configure anything. Caching is enabled by default and works transparently.

## Cache Invalidation

The cache automatically detects when recompilation is needed:

- **Source changes**: if you edit a module's `.cl` file, it is recompiled on the next run.
- **Dependency changes**: if a module you import changes, modules that depend on it are also recompiled.
- **Compiler changes**: if the compiler itself is rebuilt, all cached modules are invalidated.

You never need to manually invalidate individual modules. The cache is conservative -- when in doubt, it recompiles.

## Caching in the REPL

The REPL also uses the module cache. When you import a module in the REPL, its cached `.o` file is loaded if available, avoiding recompilation.

Session persistence works alongside the cache. Your REPL definitions are saved to `user.cl` in the current directory, and on restart this file is loaded as a module. Previously compiled dependencies (prelude, imported modules) are loaded from the object cache, so session restoration is fast.

When the file watcher detects a source change, the corresponding cache entry is invalidated and the module is recompiled from source. The new compiled result is written back to the cache.

## Caching with `--link`

The `--link` flag (standalone executable generation) relies on cached `.o` files. When you run `cranelisp --link myprogram.cl`, the compiler first compiles the module graph (writing `.o` files to the cache), then links those cached objects into a native binary. For this reason, `--link` cannot be combined with `--no-cache`.

## Disabling the Cache

To run without caching, pass the `--no-cache` flag:

```
cargo run -- --no-cache --run myprogram.cl
```

This compiles every module from source, ignoring any cached artifacts. The `--no-cache` flag only applies to batch mode (`--run`).

## Clearing the Cache

To clear all cached artifacts, delete the `.cranelisp-cache/` directory:

```
rm -rf .cranelisp-cache/
```

The next run will recompile everything and repopulate the cache.

## Version Control

The `.cranelisp-cache/` directory contains machine-specific compiled artifacts and should not be committed to version control. Add it to your `.gitignore`:

```
.cranelisp-cache/
```
