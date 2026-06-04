# 11. Standard Library (Non-Normative)

> **This section is non-normative.** It describes the constraints and conventions a standard library for Cranelisp must satisfy. The reference implementation's standard library is documented separately in the user guide.

The Cranelisp language does not mandate a specific standard library. Any conforming implementation MAY provide a different set of library modules, provided it satisfies the language-level guarantees defined in Sections 1–10 and 12. This section describes those guarantees from the perspective of a standard library author.

## 11.1 Language Guarantees to Library Authors [Tested tests/stdlib.rs::prelude_loads_without_errors]

The language guarantees the following regardless of which standard library (if any) is provided:

- **Compiler-seeded synthetic modules**: The `primitives` and `macros` modules are always available. Their contents are normatively specified in [Section 8.9](08-modules.md#89-synthetic-modules) and [Section 9.1](09-macros.md#91-sexp-data-model).

- **Module search order**: The implementation searches for library modules in the locations described in [Section 8.11](08-modules.md#811-lib-directory). A project may shadow any library module by providing a file with the same name in the project root.

- **Implicit prelude injection**: When a module named `prelude` is found on the search path, the compiler injects `(import [prelude [*]])` for all user modules (normatively defined in [Section 8.8](08-modules.md#88-prelude)). An empty prelude is valid — the language does not require the prelude to contain anything.

- **Special forms**: The structural special forms (`defn`, `deftype`, `deftrait`, `impl`, `defmacro`, `let`, `if`, `fn`, `match`, `mod`, `import`, `export`, `platform`) and `trace` are all **root special forms** — parser keywords with distinct syntax, always available without import and with no module path. `trace` produces a distinct trace node; the `Trace` / `TraceCall` types and the field accessors it returns ARE `primitives`-module entries that DO require import — the deliberate form/ADT asymmetry, mirroring `Sexp`-in-`macros` (see [Section 3.2.4](03-types.md#324-trace-type)).

## 11.2 Compiler-Seeded Types [Tested tests/ring4_trace.rs::trace_type_importable_from_primitives, tests/ring4_trace.rs::trace_field_accessors_importable, tests/io.rs::io_pure_int_type]

The following types are seeded by the compiler into synthetic modules. A standard library author does not need to define them — they are always present. They are language-level requirements normatively specified in [Section 3](03-types.md), [Section 8.9](08-modules.md#89-synthetic-modules), and [Section 9.1](09-macros.md#91-sexp-data-model):

| Module | Type | Description |
|---|---|---|
| `primitives` | `Int`, `Bool`, `String`, `Float` | Primitive scalar types |
| `primitives` | `(Vec a)` | Built-in resizable array |
| `primitives` | `(IO a)` | Effectful computation (3-constructor ADT: `Pure`, `Effect`, `Bind`) |
| `primitives` | `Trace` | Execution trace tree (1-constructor ADT: `TraceCall`). NOT auto-imported. |
| `macros` | `Sexp` | S-expression ADT for macro system |
| `macros` | `(SList a)` | Cons-list for S-expression manipulation |

Names in these modules are available via qualified reference (`primitives/add-i64`, `macros/SexpSym`) or by importing them (`(import [primitives [*]])`).

## 11.3 Bootstrapping Order [Tested tests/stdlib.rs::prelude_loads_without_errors, tests/macros.rs::macro_uses_another_batch]

A standard library that provides macros must be compiled with care because macro definitions and the types they operate on form a circular dependency. The two-pass bootstrapping order resolves this:

1. **Pass 1 — Type registration**: All `deftype` forms in the module are scanned and registered in the type checker. This makes constructors and auto-generated field accessors available to macro bodies compiled in Pass 2.

2. **Pass 2 — Sequential compilation**: Forms are processed in source order:
   - `deftype` forms are skipped (already registered).
   - `defmacro` forms are compiled (with expansion of any earlier macros in their bodies) and immediately registered in the macro environment. Each macro is available to all subsequent forms in the same file.
   - All other forms are macro-expanded, built into AST, type-checked, and compiled.

This ordering means a `defmacro` form can reference:
- Any type or constructor from the same file (registered in Pass 1).
- Any function or macro defined earlier in the same file.

Forward references to macros are not supported — a macro must appear before the code that uses it.

## 11.4 Writing a Standard Library [Tested tests/stdlib.rs::prelude_loads_without_errors]

Practical notes for library authors:

**Sexp types**: Library modules that implement macros using `match` on Sexp variants (e.g., `match arg [(SexpList items) ...]`) MUST include `(import [macros [*]])` or use fully qualified names (`macros/SexpList`). The `macros` module is not auto-imported. Quasiquote-based macros (`\`(if ~cond ~then ~else)`) do not require the import because the expander emits qualified references automatically.

**Primitives**: Library modules that need compiler-seeded functions (arithmetic, string operations, Vec operations) SHOULD import `(import [primitives [*]])`. The `primitives` module is the host for all inline and extern primitives.

**Module compilation order**: Modules compile in topological order (Section 8.10). A macro defined in `core.syntax` is available to `core.collections` if `core.collections` imports `core.syntax`. Library authors must ensure the module dependency graph is acyclic.

**The `~@` operator**: The unquote-splicing operator (`~@expr`) requires `sconcat` to be resolvable as `core.syntax/sconcat`. A standard library that uses `~@` in macro bodies must provide this qualified path, or the generated expansion code will fail to compile. The reference implementation satisfies this by providing `core.syntax` with a public `sconcat` function.

**Prelude design**: The prelude module is the mechanism by which library names become globally available. A standard library SHOULD provide a `prelude.cl` that re-exports the names it considers universally useful. The prelude itself must not import the prelude (it is excluded from implicit prelude injection).

## 11.5 Trace Support [R4 S20]

The `trace` form is a **root special form** — always available with no import and no module path (see [Section 2.3.10](02-grammar.md#2310-trace----execution-trace) and [Section 3.2.4](03-types.md#324-trace-type)); it is NOT a `primitives` entry and cannot be re-exported. The `Trace` ADT, `TraceCall` constructor, and field accessor functions (`name`, `params`, `result`, `children`, `nanos`) ARE compiler-seeded in the `primitives` module and are NOT auto-imported (the deliberate form/ADT asymmetry, see [Section 3.2.4](03-types.md#324-trace-type)). A standard library SHOULD re-export the ADT names and provide additional display functions through a `core.trace` module:

```clojure
;; stdlib/core/trace.cl
(export [primitives [Trace TraceCall name params result children nanos]])

;; Display functions defined here:
;; trace-show-tree :: Trace -> String  — full indented call tree
;; trace-show :: Trace -> String       — single-node summary: "(name p1 ...) => result [Xms]"
;; trace-call-string :: Trace -> String — call signature: "(name p1 p2 ...)"
```

Users import the combined package: `(import [core [trace [*]]])` brings in the re-exported `Trace` ADT names and the display functions together (the `trace` form itself is always available without import). These are not part of the prelude because tracing is a developer tool, not a general-purpose facility.
