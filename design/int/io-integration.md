# IO Integration Design — Sprint 16 (D1b, I3, I6, I7)

This document covers the `/int` tasks for Sprint 16: surfacing builtin docstrings (D1b), platform DLL loading (I3), batch IO entry (I6), and REPL IO (I7).

## References

- `spec/10-io.md` — IO model specification
- `repl/spec.md §1.2` — IO display format: `:primitives/IO inner_value`
- `sprints/SPRINT.md` — Architecture Review (I3, I6, I7 decisions, concern #3)
- `sketch/src/platform.rs` — platform path resolution
- `sketch/src/batch.rs` — `load_and_register_platform()`, `compile_project_pipeline()`
- `sketch/src/intrinsics.rs` — `IoTask::run()` trampoline
- `sketch/src/repl/input.rs:796` — REPL IO forcing
- `sketch/src/jit.rs:1224-1236` — batch `call_main()` IO forcing

---

## D1b: Builtin Docstrings Display

### Problem

Special forms already carry a `description` field in `DefKind::SpecialForm`, and `format_special_form_display()` surfaces it. Primitives (`DefKind::Primitive`) currently have no docstring field. D1a (/typecheck) adds `docstring: Option<String>` to `DefKind::Primitive`. D1b surfaces both special form descriptions and primitive docstrings through `/doc` and the universal output format.

### Changes to `handle_doc` (`src/repl.rs:1651`)

The current `handle_doc` handles `ModuleEntry::Macro`, `ModuleEntry::Def` (user functions), and `ModuleEntry::TraitDecl`, but does not check `DefKind` within a `Def` entry. Special forms and primitives are both stored as `ModuleEntry::Def` with different `DefKind` variants.

Change `handle_doc` to:

1. **For `ModuleEntry::Def`**: inspect the `kind` field.
   - `DefKind::SpecialForm { description }` — display the description as the docstring.
   - `DefKind::Primitive { docstring: Some(doc), .. }` — display the primitive docstring.
   - `DefKind::Primitive { docstring: None, .. }` — display "no docstring".
   - `DefKind::UserFn { .. }` — fall through to existing `docstring` field on `ModuleEntry::Def`.
   - `DefKind::Overloaded { .. }` — fall through to existing `docstring` field.

2. The output format for `/doc` follows the existing pattern: `{name}: "{docstring}"` or `{name}: no docstring`.

### Changes to Universal Output Format

The universal output format already includes `; classification - docstring` via `append_docstring_comment()`. The `format_entry_signature()` function at line 2227 already handles the `; defn - docstring` pattern for user functions and calls `format_special_form_display()` for special forms (which includes ` ; special form - description`).

For primitives, `format_entry_signature()` currently formats them as regular `Def` entries with `; defn`. This needs refinement:

1. When `DefKind::Primitive`, use `; primitive` as the classification instead of `; defn`.
2. Append the primitive's docstring via `append_docstring_comment()`.

Result:
```
user> /sig add-i64
:(Fn [primitives/Int primitives/Int] primitives/Int) primitives/add-i64 ; primitive - Add
```

### Where Changes Go

All changes are in `src/repl.rs`:
- `handle_doc()` (line 1651) — add `DefKind` inspection for special forms and primitives.
- `format_entry_signature()` (line 2227) — use `; primitive` classification for `DefKind::Primitive`, append docstring.
- No changes to `format_special_form_display()` — it already works correctly.

### Acceptance

- `/doc if` shows: `if: "Conditional expression — evaluates then or else branch based on condition"` (or whatever description text is registered).
- `/doc add-i64` shows: `add-i64: "Add"` (from spec appendix-a-builtins.md §A.3 Description column).
- `/sig add-i64` includes `; primitive - Add`.

---

## I3: Platform DLL Loading

### Overview

Platform DLL loading bridges the `(platform stdio)` declaration to runtime availability of platform functions (`print`, `read-line`). The integration layer is responsible for:

1. Recognizing `(platform name)` declarations during module processing.
2. Resolving the DLL path using the three-tier search convention.
3. Loading the DLL, validating the manifest, and registering functions.
4. Making platform functions available as primitives in the typechecker.

### Where in the Pipeline

Platform declarations are processed **after module declarations are extracted but before compilation**. The sketch demonstrates this ordering in `batch.rs:157-168`: it iterates all modules and processes platform declarations before the compilation loop.

In the reimplementation:

**Batch mode (`compile_module_graph`)**: After `discover_module_graph()` returns and before the per-module compilation loop, iterate all modules in compile order and process any `(platform name)` declarations. This requires `ModuleStructure` (or `ModuleNode`) to carry platform declarations extracted during discovery.

**REPL mode**: When the user enters `(platform stdio)`, intercept it in `eval()` before AST building (similar to how `is_defmacro` and `is_import_form` are intercepted). The sketch's REPL handles this at `repl.rs:1200-1278`.

### Platform Declaration Extraction

The frontend's `extract_module_declarations()` already handles `(mod name)`, `(import ...)`, and `(export ...)` declarations. It needs to also extract `(platform name)` declarations.

Add to `ModuleStructure`:
```rust
pub platform_decls: Vec<PlatformDecl>,
```

Where `PlatformDecl` is:
```rust
pub struct PlatformDecl {
    pub name: String,
    pub span: Span,
}
```

The frontend extracts `(platform name)` forms during `extract_module_declarations()` and removes them from the remaining sexps (they are not AST-building forms). The `ast_builder` already rejects `(platform ...)` if it reaches AST building (sketch: `ast_builder.rs:94`).

### Three-Tier Search Path

Per /arch decision I3 in the sprint Architecture Review:

```
1. CRANELISP_PLATFORM_PATH env var (colon-separated directories)
2. ./platforms/ relative to project_root
3. target/debug/ then target/release/ (Cargo build output, development convenience)
4. ~/.cranelisp/platforms/ (user-global install)
```

Direct path (containing `/` or `.dylib`/`.so`/`.dll`) bypasses search.

Implementation: `resolve_platform_path(name: &str, project_root: &Path) -> Option<PathBuf>` in a new `src/platform.rs` module (or inline in `pipeline.rs`). The sketch's `platform.rs` implements items 2-4; add item 1 (env var).

The function:
1. Check if name looks like an explicit path (contains `/` or platform extension). If so, return it directly if it exists.
2. Check `CRANELISP_PLATFORM_PATH` env var. Split by `:`, search each directory for `{name}.{ext}`.
3. Check `{project_root}/platforms/{name}.{ext}`.
4. Check `target/debug/lib{cranelisp_name}.{ext}` and `target/release/lib{cranelisp_name}.{ext}`.
5. Check `~/.cranelisp/platforms/{name}.{ext}`.

Platform extension: `.dylib` (macOS), `.so` (Linux), `.dll` (Windows).

Cargo build output filename: `lib{cranelisp_name}.{ext}` where `cranelisp_name = "cranelisp_" + name.replace('-', '_')`.

### DLL Loading and Registration

`load_and_register_platform()` in `src/pipeline.rs` (shared by batch and REPL):

```rust
pub fn load_and_register_platform(
    tc: &mut TypeChecker,
    jit: &mut Jit,
    platform_name: &str,
    project_root: &Path,
    span: Span,
) -> Result<(), CranelispError>
```

Steps:
1. **Resolve path**: Call `resolve_platform_path(platform_name, project_root)`.
2. **Load DLL**: Call `jit.load_platform(&dll_path)` — this is a backend method that uses `libloading` to open the shared library, calls the `cranelisp_platform_manifest` entry point, validates ABI version, initializes host callbacks, and extracts `OwnedPlatformFnDescriptor` values.

   > **ABI v9 cutover (S97, ctx-vtable handle model; supersedes FIXME 0482) — `ABI_VERSION = 9`;
   > refuse v8 manifests.** The "validates ABI version" step compares the manifest's self-reported
   > ABI version against the host's `ABI_VERSION`, which the v9 cut bumps **8 → 9**. The
   > layout-breaking changes that land atomically in the same change-set are the `ctx`-vtable
   > additions — `HostCtx.{acquire, retire}` fn-pointers + the `Acquire` result enum +
   > `ConcurrencyDescriptor.role` (consuming one `_reserved` byte, offsets unchanged);
   > **`PollFn`/`Poll` are UNCHANGED**, and there is **no** `ResourceDesc`/`desc_out`/value-header
   > slot (`platform-interface.md §6.8.0b`; canonical model `effect-concurrency.md §4.1.1`). A v8
   > DLL is **refused** with a `PlatformError` (version mismatch) — a **clean cutover, no
   > backward-compat shim**: the v8 leading-pair `(token, capacity)` positional convention is gone
   > (the platform now computes the token in its poll-fn and calls `ctx.acquire`), so a v8 leaf
   > cannot be driven by a v9 trampoline, and there are **no users** to migrate (the "no users"
   > rationale the S96 v8 jump already established). The constant lives in
   > `cranelisp-platform`/`-backend` (arch/platform-owned); int's loader merely propagates the
   > refusal. **Design-level note; `/dev` executes** the bump + the refusal-error wiring in the v9
   > change-set. The trampoline runtime half (the host ctx-vtable impl + tramp-owned release this
   > version gates) is `design/int/reactor.md §7`.
3. **Validate manifest name**: Check that the DLL's self-reported name matches `platform_name`.
4. **Register with typechecker**: Call `tc.register_platform(platform_name, &descriptors)` — creates a `platform.{name}` module with `Def` entries for each function, typed as `PrimitiveKind::PlatformEffect`.
5. **Insert `PlatformDecl` entry**: In the declaring module's symbol table, insert a `ModuleEntry::PlatformDecl` so `/list` and `/exports` can show it.

### Platform Function Registration in TypeChecker

The typechecker's `register_platform()` (sketch: `typechecker/primitives.rs:930-983`) creates a synthetic module `platform.{name}` and populates it with `Def` entries:

- Each descriptor's type signature is parsed from its S-expression string (e.g., `"(Fn [String] (IO Int))"`).
- Return type is validated to be wrapped in `IO` (platform boundary rule per spec §10.10.2).
- Entry is registered as `DefKind::Primitive { primitive_kind: PrimitiveKind::PlatformEffect, jit_name: Some(desc.jit_name), docstring: desc.docstring }`.
- Scheduling class is recorded for future auto-scheduling (Ring 4 Sprint 11).

### Platform Function Pointers for Trampoline

Platform functions return `Effect` nodes (not direct results). The function pointer stored in the JIT (via `jit.load_platform()`) is registered as a JIT symbol. When codegen encounters a call to a platform function, it generates a call to the JIT symbol, which returns an `Effect` node containing a thunk closure. The trampoline later executes the thunk.

The function pointer flow:
1. DLL exports: `print_impl(alloc: extern "C" fn(i64) -> i64, arg: i64) -> i64`
2. `jit.load_platform()` registers this function pointer as a JIT symbol with the platform function's JIT name.
3. Codegen emits a call to the JIT symbol. The platform function constructs an `Effect` node using the host allocator callback and returns a pointer to it.
4. The trampoline reads the `Effect` node's thunk pointer and calls `call_effect_thunk()` to execute the closure.

### Batch vs REPL Integration

**Batch** (`compile_module_graph`): Add a platform-loading pass between `discover_module_graph()` + `toposort()` and the per-module compilation loop. Iterate `order`, look up each module's `platform_decls`, and call `load_and_register_platform()`.

```rust
// After toposort, before compilation loop:
for module_path in &order {
    let node = &graph.nodes[module_path];
    for platform_decl in &node.platform_decls {
        load_and_register_platform(
            &mut tc, &mut jit,
            &platform_decl.name, &graph.project_root,
            platform_decl.span,
        )?;
    }
}
```

Note: `ModuleNode` needs a `platform_decls: Vec<PlatformDecl>` field, populated during `discover_module_recursive()`.

**REPL**: Add a `(platform ...)` interceptor in `eval()`, similar to `is_import_form()`. When detected, call `load_and_register_platform()` with the REPL session's `project_root`. Then return a `ReplResult` confirming the load:

```
user> (platform stdio)
; loaded platform: stdio v1 (2 functions)
; use (import [platform.stdio [*]]) to bring into scope
```

### Validation: Entry-Module-Only

Per spec §10.9.1, `(platform ...)` is only valid in the entry module. In batch mode, the entry module is the file passed to `--run`. If a non-entry module contains `(platform ...)`, emit a compile-time error.

In the REPL, the "entry module" is the current module. Platform declarations are always valid in the REPL because every REPL input is effectively in the entry context.

---

## I6: Batch IO Entry

### Overview

Batch programs with IO effects define `main :: (Fn [] (IO _))`. After `main()` returns an IO tree, the trampoline forces it, and the inner result determines the exit code.

### `main` Validation

Currently, `compile_module_graph()` finds the entry point via `find_entry_defn()`, which returns the last zero-arg defn. For IO programs, `main` must:

1. Exist as a zero-arg function.
2. Return `IO _` (any inner type).

The validation happens at the type level after typechecking. After the compilation loop, check the entry defn's type:

```rust
let returns_io = matches!(&entry_result_type, Type::ADT(name, _) if name.as_ref() == "IO");
```

This does NOT reject non-IO `main` — pure batch programs are still valid (they just don't run the trampoline). The spec says `main` MUST return `IO _`, but for backward compatibility with Ring 0-3 programs that have no IO, we defer enforcement until the prelude includes IO (which it will after I5).

### Trampoline Invocation

After `main()` executes and returns an i64 result:

```rust
let value = func();

if returns_io {
    // Force the IO tree via trampoline.
    // SAFETY: value is a valid IO tree pointer (Pure/Effect/Bind node).
    let inner_value = unsafe { cranelisp_runtime::IoTask::from_raw(value) }.run();
    // Exit code from inner value
    let exit_code = determine_exit_code(inner_value, &inner_type);
    (inner_value, entry_result_type)
} else {
    (value, entry_result_type)
}
```

The trampoline (`IoTask::run()`) lives in `cranelisp-runtime` (per /arch decision I2). It processes the IO tree iteratively: Pure returns the value, Effect executes the thunk, Bind pushes continuation and recurses on inner.

### Exit Code Determination

Per spec §10.6.1:
- `IO Int` — use the integer value as the process exit code.
- Other inner types — exit code 0.

```rust
fn determine_exit_code(inner_value: i64, result_type: &Type) -> i32 {
    match result_type {
        Type::ADT(name, args) if name.as_ref() == "IO" => {
            match args.first() {
                Some(Type::Int) => inner_value as i32,
                _ => 0,
            }
        }
        _ => 0,
    }
}
```

This function inspects the static type (known at compile time), not the runtime value. The inner type is extracted from `entry_result_type` which is `IO Int` or `IO String` etc.

### IO Tree Liveness Invariant (/arch concern #3)

The trampoline reads IO node fields by raw pointer. The IO tree must remain live (RC > 0) for the duration of the trampoline run. In batch mode, `main()` returns the IO tree pointer as an i64. This value is held in a local variable while the trampoline runs. The tree is live because:

1. `main()` returns the tree. The return value holds a reference.
2. The trampoline processes the tree immediately, before any code path could dec the reference.
3. Once the trampoline completes, the process exits — no cleanup needed.

No special action is required to maintain this invariant in batch mode. The local variable holding `value` keeps the root alive.

### Integration Point

The exit code needs to propagate to `main.rs` where `std::process::exit()` is called. Currently, `compile_module_graph()` returns `CompiledModuleGraph { value, ty, warnings }`. The caller in `main.rs` can use `determine_exit_code(result.value, &result.ty)` to compute the process exit code when in `--run` mode.

---

## I7: REPL IO

### Overview

When the user enters an IO expression at the REPL, the trampoline runs inline and effects execute immediately. The inner result is then displayed with the IO type wrapper.

### Detection

After `execute_expr()` returns a `ReplResult`, check if the result type is `IO`:

```rust
let is_io = matches!(&result.ty, Type::ADT(name, _) if name.as_ref() == "IO");
```

This check happens in `eval_and_display()` (line 1428), which receives the `ReplResult` from `session.eval()`.

### Trampoline Execution

When the eval result is IO-typed:

1. **Force the IO tree**: Call `IoTask::from_raw(result.value).run()` — this executes all effects in the tree (printing to stdout, reading from stdin, etc.) and returns the inner value.
2. **Extract inner type**: From `result.ty` (which is `Type::ADT("IO", vec![inner_ty])`), extract `inner_ty = args[0]`.
3. **Format display**: Use `format_result_value(inner_value, &inner_ty, ...)` to format the inner value, then wrap in the IO type display.

### Display Format

Per `repl/spec.md §1.2`:
```
user> (print "hello")
hello
0 :: (IO Int)
```

The trampoline execution produces the side effect (`hello` printed to stdout). Then the display shows the inner value with the IO wrapper type. The sketch implements this at `repl/input.rs:796-806`:

```rust
if matches!(&resolved, Type::ADT(name, _) if name == "IO") {
    let inner_val = unsafe { IoTask::from_raw(result) }.run();
    let inner_ty = match &resolved {
        Type::ADT(_, args) if !args.is_empty() => args[0].clone(),
        _ => resolved.clone(),
    };
    let value_str = format_result_value(inner_val, &inner_ty, &self.tc);
    println!("{} :: {}", value_str, formatted_type);
}
```

In the reimplementation, this logic goes in `eval_and_display()`:

```rust
if is_io {
    // Force the IO tree — side effects happen here.
    // SAFETY: result.value is a valid IO tree pointer.
    let inner_val = unsafe { cranelisp_runtime::IoTask::from_raw(result.value) }.run();
    let inner_ty = match &result.ty {
        Type::ADT(_, args) if !args.is_empty() => args[0].clone(),
        _ => result.ty.clone(),
    };
    let display = format_result_value(inner_val, &inner_ty, type_defs, type_modules);
    // Reformat with IO wrapper type
    let type_str = format_type_qualified(&result.ty, type_modules);
    writeln!(stdout, ":{type_str} {display}")
} else {
    // Existing non-IO display path
}
```

Wait — the display format per spec §1.2 shows `0 :: (IO Int)`, but the reimplementation uses `:Type value` format everywhere (per universal output format §1.1). The IO display should follow the same pattern:

```
user> (print "hello")
hello
:(primitives/IO primitives/Int) 0
```

The `hello` line is a side effect from the trampoline. The result line shows the full IO type with the inner value. Check `repl/spec.md §1.2` for the exact format — it shows `:primitives/IO inner_value` which suggests a simplified display. The implementation should match whatever the spec says after /repl finalizes the IO display format.

### IO Tree Liveness Invariant (/arch concern #3)

In the REPL, the eval result holds a reference to the IO tree while the trampoline runs. The flow:

1. `execute_expr()` calls the compiled function, gets `value: i64` (IO tree pointer).
2. Returns `ReplResult { value, ty, ... }`.
3. `eval_and_display()` receives the `ReplResult`, which owns `value`.
4. Calls `IoTask::from_raw(result.value).run()` — trampoline runs while `result` (and thus `value`) is alive.
5. After `run()` returns, the IO tree can be freed (process exits scope).

This is safe because `result.value` is an i64 copy of the pointer, and the IO tree's RC is maintained by normal scope rules. The tree was allocated during the eval, returned as the result, and its RC reflects that it is still referenced (the compiled code's return value keeps it alive until the trampoline consumes it).

**Subtlety**: The trampoline does NOT dec IO nodes — it reads fields by raw pointer. The IO tree is freed when its RC reaches zero through normal scope exit in the compiled code. Since the compiled expression returns the IO tree (incrementing its RC via the return path), the tree stays alive until the trampoline completes and the calling code's stack frame is reclaimed. In practice, the REPL never explicitly dec's the returned value — it reads the raw i64 and moves on. This means IO trees from REPL expressions leak (their RC never reaches zero). This is acceptable for REPL use because:

1. IO trees are small (a few nodes per expression).
2. The REPL session accumulates many such leaks over its lifetime, which is bounded.
3. Fixing this properly requires the REPL to emit RC dec after the trampoline completes, which is a general REPL value cleanup task (not IO-specific).

### Definition-Producing IO

When a `defn` returns IO (e.g., `(defn main [] (print "hello"))`), the REPL currently evaluates zero-arg defns and shows their result. For IO-returning zero-arg defns:

1. The defn is compiled and its result type includes IO.
2. The zero-arg call returns an IO tree.
3. The same IO detection and trampoline logic applies.

This is handled uniformly because `execute_defn()` for zero-arg functions goes through the same result path.

### Error Recovery

If the trampoline panics (e.g., unknown IO tag, null pointer), the REPL must not crash. Wrap the trampoline call in `std::panic::catch_unwind()`:

```rust
let trampoline_result = std::panic::catch_unwind(|| {
    unsafe { cranelisp_runtime::IoTask::from_raw(result.value) }.run()
});
match trampoline_result {
    Ok(inner_val) => { /* display normally */ }
    Err(_) => { writeln!(stdout, "error: IO trampoline panicked"); }
}
```

This prevents a malformed IO tree from killing the REPL session.

---

## Implementation Order

1. **D1b** (Wave 2) — depends on D1a. Pure display changes, no new infrastructure.
2. **I3** (Wave 4) — depends on I4 (platform DLL exists). New `resolve_platform_path()`, `load_and_register_platform()`, platform interception in both batch and REPL.
3. **I6** (Wave 4) — depends on I2 (trampoline exists), I3 (platforms loaded). Add IO detection + trampoline call in batch path, exit code propagation.
4. **I7** (Wave 4) — depends on I2, I3. Add IO detection + trampoline call in REPL eval display path.

I6 and I7 share the IO detection pattern (`matches!(&ty, Type::ADT(name, _) if name == "IO")`). Extract as a helper:

```rust
fn is_io_type(ty: &Type) -> bool {
    matches!(ty, Type::ADT(name, _) if name.as_ref() == "IO")
}

fn extract_io_inner_type(ty: &Type) -> Type {
    match ty {
        Type::ADT(_, args) if !args.is_empty() => args[0].clone(),
        _ => ty.clone(),
    }
}
```

---

## Files Changed

| File | Change | Status |
|------|--------|--------|
| `src/repl.rs` | D1b: `format_entry_signature` uses `; primitive` for `DefKind::Primitive`. I3: `eval_platform()`, platform_symbols field, `Jit::new_with_symbols` in compile_and_register_defn, `compile_expr_with_got_and_symbols` for expressions. I7: `is_io_type()`, `extract_io_inner_type()`, `force_io_and_format()`, `format_value_only()` — IO detection in `eval_and_display()`, trampoline with `catch_unwind`, inner value display. | D1b: DONE, I3: DONE, I7: DONE |
| `src/pipeline.rs` | I3: pre-scan entry module for platform decls, load before JIT creation, `filter_platform_forms`, `scan_for_platform_decls`. I6: `is_io_type()`, `extract_io_inner_type()`, `determine_exit_code()`, trampoline invocation in `compile_module_graph()`. | I3: DONE, I6: DONE |
| `src/platform.rs` (new) | I3: `resolve_platform_path()`, `load_platform_dll()`, `register_platform_in_tc()`, `load_and_register_platform()`, `is_platform_form()`, `extract_platform_name()`, `parse_platform_type_sig()` + 14 tests. | I3: DONE |
| `src/lib.rs` | I3: `pub mod platform;` | I3: DONE |
| `Cargo.toml` | I3: `libloading = "0.8"` dependency | I3: DONE |
| `crates/cranelisp-backend/src/lib.rs` | I3: `compile_expr_with_got_and_symbols()` — new function accepting extra JIT symbols for platform function resolution. | I3: DONE |
| `crates/cranelisp-types/src/module.rs` | D1b: docstrings already on `ModuleEntry::Def.docstring` (done by D1a). No changes needed. | D1b: N/A |
| `src/main.rs` | I6: exit code propagation via `determine_exit_code()`. | I6: DONE |
