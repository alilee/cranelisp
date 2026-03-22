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
