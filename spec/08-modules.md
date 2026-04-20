# 8. Modules [Tested]

This section defines the module system of Cranelisp -- how source files map to modules, how names are imported and exported across module boundaries, and how name resolution operates in the presence of multiple modules.

## 8.1 File-to-Module Mapping [Tested crates/cranelisp-frontend/src/module_extract.rs::test_module_path_preserved]

Each `.cl` source file defines exactly one module. The module's identity is derived from the file's path relative to the project root or library directory.

### 8.1.1 Naming Rules

- A file `foo.cl` in the project root defines module `foo`.
- A file `foo/bar.cl` defines module `foo.bar` (a submodule of `foo`).
- The hierarchy separator in module names is `.` (dot).
- Hyphens in filenames are preserved in module names: `my-util.cl` defines module `my-util`.

The entry file (the file passed to the compiler or REPL) defines the **root module**. In batch mode, this is the file containing `main`.

Module identity is determined solely by the file's path relative to the project root. A `(mod name)` declaration does **not** rename the loaded module — it triggers loading of whatever file is found at the resolved path, and that file's module identity is the path of the file itself. If `main.cl` contains `(mod util)` and the search (Section 8.2.5) finds `util.cl` at the project root, the loaded module is named `util` (not `main.util`). If instead `main/util.cl` is found, the loaded module is named `main.util`.

```
project/
  main.cl             ; root module (entry point)
  util.cl             ; module "util"
  util/
    helpers.cl        ; module "util.helpers"
  config.cl           ; module "config"
```

### 8.1.2 No Inline Module Declaration

A file's module identity is determined entirely by its filesystem path. There is no in-file declaration of module identity -- a file does not name itself.

## 8.2 Module Declaration [Tested tests/ring2::single_file_via_run_project]

The `mod` special form declares that the current module has a submodule, and triggers loading of the corresponding `.cl` file.

```ebnf
mod_decl = '(' 'mod' symbol ')'
         | '(' 'mod' symbol form+ ')'
         | '(' 'mod-' symbol ')'
         | '(' 'mod-' symbol form+ ')'
```

### 8.2.1 Public Submodule Declaration

```clojure
(mod handler)
```

Declares `handler` as a public submodule of the current module. If the current module is `app`, this makes `app.handler` available.

### 8.2.2 Inline Submodule Declaration

```clojure
(mod test
  (import [super [*]])
  (defn test-add [] (assert-eq 7 (add 3 4))))
```

Declares `test` as a submodule and provides its body inline. On first compilation, the implementation MUST:

1. Create the submodule backing file (`{parent_dir}/{stem}/{name}.cl`) containing the inline body, formatted as source text. Create the directory if needed.
2. Rewrite the parent file, replacing `(mod name form1 form2 ...)` with `(mod name)`.
3. Proceed with standard file-based module loading for the new submodule file.

After extraction, the submodule is indistinguishable from one created manually. The inline form is a **one-time creation syntax** — subsequent compilations use the extracted file. Re-entering the inline form overwrites the extracted file.

In the REPL, an inline `(mod name ...)` writes the backing file and loads the submodule via the standard file-based path.

### 8.2.3 Private Submodule Declaration [Tested+Neg tests/ring2.rs::neg_private_submodule_not_importable_from_peer — FAILING: /int gap, `(mod- ...)` protection not enforced cross-module]

<!-- FIXME(/spec): Sprint 58 Wave 4 Step 5d (i) closed the /int gap. The test
     `tests/ring2.rs::neg_private_submodule_not_importable_from_peer` now PASSES;
     the import resolver emits the spec-mandated error
     "cannot import from private submodule '...': declared private by '...' via
     (mod- internal); importer '...' is not within the '...' subtree (spec §8.2.3)".
     ring4p.demo Wave 6 plays the rejection live. Drop the FAILING tag and keep
     the [Tested+Neg ...] annotation with the test name. Filed by /repl during
     Sprint 58 Wave 6 audit. -->

<!-- FIXME(/int): Private submodule enforcement (§8.2.3 MUST NOT) is not yet implemented — `tests/ring2.rs::neg_private_submodule_not_importable_from_peer` asserts that a peer module importing from a `(mod- internal)` declaration MUST fail compilation, but the import currently succeeds (compilation is Ok where it must be Err). Visibility check lives in the import resolver; the path-based `(mod- ...)` marker is parsed but not propagated to the module's visibility flag. Filed by /qa during Sprint 57 Wave 5. -->


```clojure
(mod- internal)
```

Declares `internal` as a private submodule, accessible only within the declaring module and its submodule subtree. Other modules MUST NOT import from or reference names in a private submodule.

### 8.2.5 File Resolution [Tested tests/ring2::module_missing_file_error]

When `(mod name)` appears in a file (after inline extraction, if applicable), the implementation MUST resolve the corresponding `.cl` file to the child directory path only:

- **Child directory**: `{parent_dir}/{stem}/{name}.cl` -- where `{stem}` is the declaring file's name without extension.

For example, if `app.cl` contains `(mod handler)`, the implementation resolves to `app/handler.cl`. If this file does not exist, it is a compile-time error.

Sibling files (e.g., `handler.cl` in the same directory as `app.cl`) are NOT considered. A sibling file is a peer module, not a submodule. Allowing sibling fallback would create ambiguity: the same file could be both `app.handler` (via `mod`) and root module `handler` (via the search path in §8.11.2), violating §8.1's principle that file path determines module identity. To reference a peer module, use `import` with the module's own name (e.g., `(import [handler [...]])`), not `mod`.

### 8.2.6 Placement [Tested tests/ring2::module_cycle_detection, crates/cranelisp-frontend/src/module_extract.rs::test_mixed_forms]

`mod` declarations MUST appear as top-level forms. They are extracted from the raw S-expression stream before macro expansion. A `mod` form encountered in any other position (inside a function body, let binding, etc.) is an error.

**Example -- multi-module project:**

```clojure
;; main.cl (entry point)
(mod util)
(mod math)

(defn main []
  (print (show (util/helper 42))))
```

```clojure
;; util.cl
(defn helper [:Int x] :Int (+ x 1))
```

```clojure
;; math.cl
(defn double [:Int x] :Int (* x 2))
```

## 8.3 Import [Tested tests/ring2::import_specific_names]

The `import` special form brings names from other modules into the current module's scope as bare (unqualified) symbols.

```ebnf
import_form  = '(' 'import' '[' import_entry+ ']' ')'
import_entry = module_spec names_list
module_spec  = symbol                            ; bare module path
             | 'super'                           ; parent module reference
             | '(' symbol symbol ')'             ; (module alias) pair
names_list   = '[' name+ ']'                     ; specific names
             | '[' '*' ']'                        ; all public names
             | '[' member_glob ']'               ; all members of a type or trait
             | '[' ']'                            ; no names (alias-only)
member_glob  = symbol '.*'                       ; e.g. Display.*
```

### 8.3.1 Specific Name Import

```clojure
(import [core.option [Some None]])
```

Imports `Some` and `None` from module `core.option` as bare names. Each listed name MUST be a public name in the source module; otherwise it is a compile-time error.

### 8.3.2 Glob Import

```clojure
(import [core.math [*]])
```

Imports all public names from `core.math`. Private names (defined with `-` suffix forms) are excluded.

The `*` in `[*]` is reserved for the glob-all form and only has that meaning when it is the sole element in the names list. To import the `*` operator (multiplication) alongside other names, include it in a specific names list: `(import [core.numerics [+ - * /]])`. With multiple names present, `*` is treated as an operator symbol, not a glob.

### 8.3.3 Member Glob Import

```clojure
(import [core.fmt [Display.*]])
```

Imports all methods of trait `Display` (or all constructors of a type) as bare names. The parent name (`Display`) MUST refer to a type or trait defined in the source module.

### 8.3.4 Alias Import

```clojure
(import [(core.string str) [concat join]])
```

Imports `concat` and `join` as bare names, and registers `str` as an alias for `core.string`. The alias can then be used for qualified references: `str/split`.

### 8.3.5 Alias-Only Import

```clojure
(import [(core.option opt) []])
```

Registers `opt` as an alias for `core.option` without importing any bare names. Useful when you only want qualified access: `opt/Some`.

### 8.3.6 Null Import

```clojure
(import [core.option []])
```

Imports nothing and does not trigger module loading or resolution. Useful to suppress the implicit prelude import (§8.8.1) — an explicit `(import [prelude []])` replaces the implicit glob without loading the prelude module.

### 8.3.7 Super Import

```clojure
(import [super [*]])
```

Inside a submodule, `super` resolves to the parent module by stripping the last component from the current module's full path. For example, inside `math.test`, `super` resolves to `math`.

`super` MAY be used with any name list form (specific names, glob, member glob):

```clojure
(import [super [add double]])    ; specific names from parent
(import [super [*]])             ; all public names from parent
```

Using `super` in a top-level module (one with no parent) MUST produce a compile-time error.

This is the standard way for test submodules to access the code under test.

> **Known limitation — mutual-import deadlock.** `super` is supported for one-directional child → parent imports. If the parent module imports anything (directly or transitively) from a child that uses `(import [super ...])`, the compiler's form-by-form scheduler deadlocks during typechecking: the parent blocks on the child's signatures while the child (via `super`) blocks on the parent's. A conforming implementation MAY reject this configuration with a diagnostic, but MUST NOT silently produce a non-terminating compilation. Authors SHOULD NOT construct parent↔child mutual-import cycles. Test submodules that need to enumerate their parent's symbols SHOULD use the `discover-tests` and `run-test` builtins (see [Appendix A](appendix-a-builtins.md)) — these observe the parent's symbol table at runtime without requiring a `super` import, avoiding the deadlock entirely. See `design/arch/CLAUDE.md` Decision 30 for the underlying pass-order constraint. A future language version may redesign the module-loading pass order to lift this restriction; no timeline is promised.

### 8.3.8 Multiple Module Import

Multiple modules MAY be imported in a single `import` form:

```clojure
(import [core.option [Some None]
         core.math   [*]
         core.fmt    [Display.*]])
```

Module-names-list pairs are processed left to right.

### 8.3.9 Placement

`import` forms MUST appear as top-level forms. They are extracted from the raw S-expression stream before macro expansion. An implementation MUST process `import` before compiling definitions in the same module, so that imported names are available during type checking and code generation.

A module MAY contain multiple `import` forms. Their effects accumulate: names imported by each form are merged into the module's symbol table. The conflict rules in Section 8.6.4 apply across all `import` forms — importing the same bare name from two different source modules (across any number of `import` forms) is an error.

**Example -- importing types and constructors:**

```clojure
;; main.cl
(mod types)
(import [types [Point make-point x y]])

(defn main []
  (let [p (make-point 3 4)]
    (print (show (x p)))))
```

```clojure
;; types.cl
(deftype Point [:Int x :Int y])
(defn make-point [:Int x :Int y] :Point (Point x y))
```

## 8.4 Export [Tested crates/cranelisp-frontend/src/module_extract.rs::test_export_specific, crates/cranelisp-frontend/src/module_extract.rs::test_export_glob]

The `export` special form re-exports names from imported modules, making them part of the current module's public API.

```ebnf
export_form  = '(' 'export' '[' export_entry+ ']' ')'
export_entry = symbol names_list
```

### 8.4.1 Specific Re-export

```clojure
(export [core.option [Option Some None]])
```

Re-exports `Option`, `Some`, and `None` from `core.option` through the current module.

### 8.4.2 Glob Re-export

```clojure
(export [core [*]])
```

Re-exports all public names from `core` through the current module.

### 8.4.3 Multiple Module Re-export

```clojure
(export [core       [*]
         primitives [vec-len vec-get vec-set]])
```

### 8.4.4 Semantics

A re-exported name becomes a public name of the exporting module. When another module imports from the exporting module (via `[*]` or by name), re-exported names are included.

An implementation MUST track re-export provenance so that introspection can display the original defining module, not the re-exporting module. For example, if `prelude` re-exports `print` from `platform.stdio`, introspection SHOULD display `platform.stdio/print` as the origin.

### 8.4.5 Placement

`export` forms MUST appear as top-level forms. They are extracted alongside `mod` and `import` before macro expansion.

**Example:** A standard library might organize re-exports through a shell module:

```clojure
;; stdlib/core.cl
(mod numerics)
(mod formats)
(mod collections)
(mod option)
(mod sequences)
(mod io)
(mod syntax)

(export [numerics    [*]
         formats     [*]
         collections [*]
         option      [*]
         sequences   [*]
         io          [*]
         syntax      [*]])
```

```clojure
;; stdlib/prelude.cl
(export [core       [*]
         primitives [vec-len vec-get vec-set vec-push
                     vec-map vec-reduce parse-int
                     str-concat quote-sexp]])
```

## 8.5 Qualified Names [Tested tests/ring2::module_qualified_name_resolution]

Names MAY be referenced with explicit module qualification, bypassing the need for imports.

### 8.5.1 Module-Qualified Names

```ebnf
qualified_name = module_path '/' local_name
module_path    = segment ('.' segment)*
local_name     = symbol | dotted_symbol | operator_symbol
```

The `/` separates the module path from the local name:

```clojure
util/helper             ; function 'helper' in module 'util'
core.option/Some        ; constructor 'Some' in module 'core.option'
core.math/+             ; operator '+' in module 'core.math'
```

The parser MUST distinguish qualified names from the division operator. A `/` is only a qualified separator when preceded by an alphabetic module path. `(/ 10 2)` remains the division operator because the `/` is not preceded by a symbol.

### 8.5.2 Dotted Names

The `.` within a name provides access to members of types and traits:

```clojure
Option.Some             ; constructor 'Some' of type 'Option'
Option.None             ; constructor 'None' of type 'Option'
Display.show            ; method 'show' of trait 'Display'
Num.+                   ; operator '+' of trait 'Num'
```

Dotted names resolve directly from the parent type or trait definition, bypassing the bare-name lookup. This means they work even when the bare name is ambiguous (see Section 8.6.5).

### 8.5.3 Combined Qualification

Module path and dot notation MAY be combined:

```clojure
core.option/Option.Some     ; fully qualified constructor
core.fmt/Display.show       ; fully qualified trait method
```

### 8.5.4 Auto-Loading

When a qualified name references a module that has not yet been loaded, the implementation SHOULD attempt to load that module on demand. This enables qualified references to work without explicit `import` or `mod` declarations.

In a REPL environment, qualified name references SHOULD trigger lazy loading of the referenced module.

## 8.6 Name Resolution [Tested tests/ring2.rs::name_resolution_local_shadows_module, tests/ring2.rs::module_qualified_name_resolution]

Name resolution converts source-level names into their definitions. An implementation MUST follow the resolution layers defined in this section.

### 8.6.1 Resolution Layers

Resolution proceeds through three layers, in order:

1. **Local environment**: `let` bindings, `fn` parameters, and `match` pattern variables. These are lexically scoped -- pushed on entry to a binding form and popped on exit.

2. **Module scope**: Definitions within the current module, plus names brought in via `import`. This layer consults the current module's symbol table, following `Import` and `Reexport` references to their source modules.

3. **Root module**: Special forms (`if`, `let`, `fn`, `match`, `do`, etc.) live in a distinguished root module that is always consulted. Special forms are available without import or qualification.

For qualified names (`module/name`), resolution bypasses layers 1 and 2 and goes directly to the named module's symbol table.

### 8.6.2 Import Resolution

When a bare name is encountered in module scope, the implementation resolves it by looking up the current module's symbol table:

- A `Def` entry provides the definition directly.
- An `Import` entry provides a reference to the source module and name; the implementation follows this reference.
- A `Reexport` entry likewise provides a reference to the original source, which the implementation follows.

Import/Reexport chains MUST be followed transitively until a `Def` entry is reached. An implementation SHOULD impose a depth limit to detect pathological chains.

### 8.6.3 Shadowing Rules

Local bindings shadow module-scope names:

```clojure
(import [math [pi]])
(let [pi 3]
  (+ pi 1))    ; -> 4, uses local binding
```

This is permitted without error -- local bindings are lexically scoped and always take priority through the local environment layer.

### 8.6.4 Conflict Rules

The following conflicts MUST produce compile-time errors:

- **Duplicate imports**: Two `import` forms bringing the same bare name from different source modules:

  ```clojure
  (import [math [add] util [add]])    ; error: ambiguous bare name 'add'
  ```

- **Definition over import**: A definition (`defn`, `deftype`, etc.) in the current module that has the same name as an explicitly imported name:

  ```clojure
  (import [math [add]])
  (defn add [x y] (+ x y))           ; error: definition conflicts with import
  ```

Same-source duplicates (the same name arriving through two re-export paths from the same original definition) are NOT ambiguous.

#### Explicit Imports Shadow the Implicit Prelude [R4 S20]

The implicit prelude glob (`(import [prelude [*]])`, injected per §8.8) is processed **before** any explicit imports in the module. Explicit imports — whether glob (`(import [grid [*]])`) or specific (`(import [grid [solve]])`) — shadow prelude-provided names without producing a duplicate-import error. This is intentional: explicit imports take precedence over the implicit prelude, just as inner `let` bindings shadow outer ones.

When an explicit glob import brings in a name that was already provided by the prelude, the explicit version silently replaces the prelude version. This means the module loses access to the prelude's binding for that bare name. Remediation strategies:

- **Qualified access**: Use `prelude/Some` or `primitives/Some` to reach the shadowed name.
- **Selective import**: Replace `(import [grid [*]])` with `(import [grid [solve other-fn]])` to avoid importing names that collide.
- **Explicit prelude re-import**: Add `(import [prelude [Some None]])` after the glob import to restore specific prelude names.

**Practical note**: Glob imports from modules with large public APIs can silently displace prelude bindings (e.g., a module that re-exports `Some`/`None` for convenience). When debugging unexpected type errors after adding a glob import, check whether prelude names have been shadowed.

### 8.6.5 Ambiguity and Disambiguation

When two sources register the same bare name in a module's symbol table, the name becomes **ambiguous** (poisoned). Attempting to use an ambiguous bare name MUST produce a compile-time error listing the qualified alternatives.

```clojure
;; If both Display and Debug define a 'show' method:
(show x)              ; error: ambiguous bare name 'show'
                      ;        use 'Display.show' or 'Debug.show'
```

Qualified names and dotted names always bypass ambiguity:

```clojure
(Display.show x)      ; resolves directly via trait 'Display'
(core.fmt/show x)     ; resolves directly via module 'core.fmt'
```

### 8.6.6 Qualified Name Resolution Order

For a qualified name `path/sym`, resolution proceeds:

1. If `path` matches a module alias (from an aliased import), resolve in the aliased module.
2. If `path` matches a child module of the current module, resolve there.
3. If `path` is a full module path (matching a known module), resolve directly.
4. Otherwise, it is a compile-time error: unknown module.

The target symbol MUST be public in the resolved module. Accessing a private name through a qualified reference is a compile-time error.

## 8.7 Visibility [Tested tests/ring2.rs::visibility_private_defn_not_importable, tests/ring2.rs::visibility_public_defn_importable, tests/ring2.rs::visibility_private_deftype_not_importable]

### 8.7.1 Public by Default

All definitions are public by default. Public names are accessible from other modules via `import` or qualified reference.

### 8.7.2 Private Definitions

Private variants of definition forms use a `-` suffix on the form name:

| Form | Private variant | Purpose |
|---|---|---|
| `defn` | `defn-` | Private function |
| `deftype` | `deftype-` | Private type |
| `deftrait` | `deftrait-` | Private trait |
| `defmacro` | `defmacro-` | Private macro |
| `mod` | `mod-` | Private submodule |

These are special forms, not macros.

### 8.7.3 Private Name Semantics [Tested+Neg tests/ring2.rs::neg_private_name_not_in_glob_import, tests/ring2.rs::neg_glob_import_private_not_via_qualified, tests/ring2.rs::neg_private_macro_not_importable]

A private name:

- Is accessible within the defining module.
- Is accessible within the submodule subtree of the defining module.
- MUST NOT be exported, even with `[*]` glob exports. Glob exports include only public names.
- MUST NOT be accessed via qualified reference from outside the defining module's subtree. A qualified reference to a private name from an external module is a compile-time error.

**Example:**

```clojure
;; util.cl
(defn helper [:Int x] :Int (+ x 1))         ; public
(defn- internal [:Int x] :Int (* x x))       ; private

;; main.cl
(mod util)
(import [util [helper]])   ; ok
(import [util [internal]]) ; error: 'internal' is not public in 'util'

(util/helper 42)           ; ok
(util/internal 42)         ; error: 'internal' is private
```

## 8.8 Prelude [Tested tests/stdlib::prelude_loads_without_errors, tests/modules::prelude_like_reexport_compiles]

### 8.8.1 Implicit Import

When a module's source does not reference `prelude` in any `import` or `export` form, the implementation MUST inject an implicit glob import:

```clojure
(import [prelude [*]])    ; implicit -- injected by the compiler
```

This makes all public names from the prelude available as bare symbols.

An explicit `(import [prelude [...]])` or `(export [prelude [...]])` suppresses the implicit glob. The module author may import specific prelude names, suppress the prelude entirely with a null import (§8.3.6), or re-export prelude symbols without receiving the full glob.

A `(mod prelude)` declaration does not suppress the implicit import, but the declared submodule shadows the library prelude during module resolution.

### 8.8.2 Regular Module Semantics

The prelude uses normal module resolution (Section 8.11.2) with no special search paths. It is discovered, loaded, and compiled as a regular module through the standard compilation pipeline -- it participates in the module graph like any other module and is compiled in topological order (its dependencies first, then the prelude, then user modules).

A project MAY provide its own `prelude.cl` that shadows a library prelude, since module resolution checks the project directory before the stdlib directory.

### 8.8.3 Empty Prelude

An empty prelude is valid. The core language -- primitives, special forms, type inference -- works without any prelude content. The prelude provides convenience (traits, operators, types, macros) but is not required for the language to function.

```clojure
;; A valid, empty prelude.cl
```

## 8.9 Synthetic Modules [Tested tests/ring2.rs::synthetic_primitives_module_available]

Synthetic modules are registered by the runtime without corresponding `.cl` source files. They provide compiler-seeded types, built-in functions, and platform bindings.

### 8.9.1 The `primitives` Module

The `primitives` module contains:

- **Builtin types**: `Int`, `Bool`, `String`, `Float`, `Vec`
- **The IO ADT**: `(deftype (IO a) (IOVal [:a ioval]))` -- the compiler-seeded IO type
- **Primitive functions**: The specific catalog of primitive functions is implementation-defined. See [Appendix A](appendix-a-builtins.md) for the reference implementation's catalog.

Names in `primitives` are stored in qualified form only (`primitives/add-i64`). They are NOT available as bare names unless imported through the prelude chain.

In batch mode (and REPL mode), the implicit prelude import (§8.8.1) brings primitive functions into scope as bare names, provided the prelude re-exports them. A program that uses `(add-i64 2 3)` without an explicit `(import [primitives [...]])` works correctly when the prelude is loaded and re-exports `add-i64`. Without a prelude (or with a prelude that does not re-export the needed primitives), an explicit import from `primitives` is required. [R4 S52]

### 8.9.2 The `macros` Module

The `macros` module contains the `Sexp` and `SList` algebraic data types used by the macro system:

- `Sexp` -- the S-expression ADT with constructors for integers, strings, symbols, lists, and brackets
- `SList` -- a cons-list type with `SCons` and `SNil` constructors

The `macros` module is NOT implicitly imported. The macro expander and `quote-sexp` primitive emit qualified references (`macros/SexpSym`, `macros/SCons`, etc.), so quasiquote-based macros work without importing the module. Modules that directly reference Sexp constructors (e.g., for pattern matching on macro arguments) MUST import or use qualified references eg. `(import [macros [*]])`.

### 8.9.3 Platform Modules [R4 S10]

Platform modules are loaded from dynamic libraries (DLLs) via the `platform` special form:

```clojure
(platform stdio)     ; loads platform.stdio from a DLL
```

The platform name is resolved to a DLL file via the platform DLL search order (§8.11.3). This registers a synthetic module named `platform.stdio` containing the functions exported by the platform library. Platform functions that perform side effects MUST return `IO _`.

Platform module names follow the pattern `platform.<name>`.

### 8.9.4 Availability

Synthetic modules are always known to the module system. Their names are seeded into the module name registry so that `(import [primitives [*]])` resolves without file discovery.

## 8.10 Module Compilation Order [Tested tests/ring2::module_cycle_detection]

### 8.10.1 Dependency Graph

The implementation MUST construct a dependency graph from module declarations (`mod`, `import`, `export`, `platform`) and compile modules in **topological order** -- dependencies before dependents.

### 8.10.2 Circular Dependencies

Circular dependencies MUST be detected and reported as a compile-time error. Two modules that mutually depend on each other (directly or transitively) cannot be compiled.

### 8.10.3 Whole-Module Compilation

Each module is a compilation unit. A module is fully processed -- parsed, macro-expanded, AST-built, type-checked, and code-generated -- before any module that depends on it begins compilation. This is required because macro exports and type definitions must be fully available before importers can use them.

### 8.10.4 Definition Execution Order

Within a module, definitions are processed sequentially from top to bottom. Each definition is fully compiled before the next begins. This allows macros defined earlier in a file to be used by later definitions in the same file.

Module-level expressions (definitions, trait implementations) execute at load time in definition order.

**Example:** The reference implementation's standard library compiles in this order. The specific structure is not required -- any module organization that satisfies the topological ordering constraint is valid:

```
stdlib/core/numerics.cl    ; compiled first (leaf dependency)
stdlib/core/formats.cl     ; depends on numerics
stdlib/core/collections.cl ; depends on numerics, formats
stdlib/core/option.cl      ; depends on collections
stdlib/core/sequences.cl   ; depends on numerics, collections
stdlib/core/io.cl          ; depends on primitives
stdlib/core/syntax.cl      ; depends on collections, sequences
stdlib/core.cl             ; depends on all core submodules
stdlib/prelude.cl          ; depends on core
main.cl                 ; depends on prelude (implicit)
```

## 8.11 Search Paths

### 8.11.1 Project Root [Tested tests/modules.rs::project_root_shadows_stdlib]

The **project root** is the directory containing the entry file (the `.cl` file passed to the compiler or the REPL's working directory). It anchors all relative path resolution for both modules and platform DLLs.

### 8.11.2 Module Resolution Search Order [Tested tests/modules.rs::project_root_shadows_stdlib, tests/modules.rs::stdlib_module_compiles_and_runs]

When resolving a module name to a file, the implementation MUST search in this order:

1. **Submodule of current module** -- already registered via `(mod name)` in the current module. No file search is required because the submodule was loaded when the `mod` declaration was processed.
2. **Project root** -- `{project_root}/{name}.cl`. The directory containing the entry file.
3. **Lib directories** -- `{lib_dir}/{name}.cl` for each lib directory, in order.

A module in the project root shadows a module with the same name in a lib directory. This is intentional -- it allows projects to override library modules.

The standard library is not a special language feature beyond this search mechanism. Modules named `core`, `prelude`, `std`, or anything else are ordinary Cranelisp source files found through the module search order — there is no distinction at the language level between "standard library" modules and user modules.

### 8.11.3 Platform DLL Resolution Search Order [Tested tests/wave3_g8.rs]

When resolving a platform name to a DLL (§8.9.3), the implementation MUST search in this order:

1. **Project root** -- `{project_root}/platforms/{name}.{ext}`
2. **Lib directories** -- `{lib_dir}/platforms/{name}.{ext}` for each lib directory, in order.
3. **Platform directories** -- additional directories from platform-specific configuration (§8.11.5).

The file extension `.{ext}` is platform-dependent (`.dylib` on macOS, `.so` on Linux, `.dll` on Windows). The implementation SHOULD also accept the Cargo library naming convention (`libcranelisp_{name}.{ext}`) as an alternative filename at each search location.

Platform resolution mirrors module resolution: project root is checked first, then lib directories in order. This means a project can ship platform DLLs alongside its source (`myproject/platforms/custom-io.dylib`), and a standard library can ship platforms alongside its modules (`stdlib/platforms/stdio.dylib`).

### 8.11.4 Lib Directory Configuration [Tested tests/e2e.rs::e2e_cranelisp_lib_env_overrides_stdlib (env var); project-config file NOT YET IMPLEMENTED — see FIXME(/int) below]

Lib directory locations are assembled from the following sources, in precedence order:

1. **Explicit programmatic additions** -- the implementation MUST support adding lib directories in code (e.g., via a session API). These take highest precedence and are appended to the list.
2. **Project configuration file** (e.g., `Cranelisp.toml`) MAY specify a lib directory list. When present, this takes precedence over environment and defaults.
3. **`CRANELISP_LIB` environment variable**, if set. A colon-separated list of directory paths. When set (even to empty), it fully controls the default lib directory list — no fallback is applied.
4. **Default fallback**: When neither a project configuration file nor `CRANELISP_LIB` is present, the implementation SHOULD use `{project_root}/stdlib/` as the sole default lib directory, if that directory exists.

<!-- FIXME(/int): Cranelisp.toml project configuration (§8.11.4 item 2) is spec-documented but not implemented — `src/session.rs::assemble_lib_dirs` only consults `CRANELISP_LIB` and `{project_root}/stdlib/`. A `Cranelisp.toml` in the project root is silently ignored. Either implement the loader (look for `Cranelisp.toml`, parse `lib-dirs` key, prepend to resolution list) or downgrade the spec language to "MAY" in future work. Filed by /qa during Sprint 57 Wave 5 while resolving a /qa traceability FIXME on §8.11. -->


If no sources yield any lib directories, the lib directory list is empty. No lib modules (including `prelude` and `core`) will be found. The language still functions — primitives and special forms remain available — but no standard library names are in scope.

> **Practical implication.** The project root is the directory containing the entry file. A project at `exemplar/solver.cl` has project root `exemplar/`. If `exemplar/stdlib/` does not exist and `CRANELISP_LIB` is not set, the prelude will not load. To use the standard library from a subdirectory project, either:
> - Set `CRANELISP_LIB` to point to the stdlib location (e.g., `CRANELISP_LIB=../stdlib`), or
> - Create a project configuration file that specifies the lib path, or
> - Symlink or copy `stdlib/` into the project root.

### 8.11.5 Platform Directory Configuration

Additional platform-specific search directories are assembled from:

1. **Explicit programmatic additions** -- the implementation MUST support adding platform directories in code.
2. **Project configuration file** MAY specify a platform directory list.
3. **`CRANELISP_PLATFORM_PATH` environment variable**, if set. A colon-separated list of directory paths.

These directories are searched after project root and lib directories (§8.11.3, tier 3). They are intended for platform DLLs that are not co-located with source modules — for example, system-wide installations or Cargo build output during development.

> **Development convenience.** During development, set `CRANELISP_PLATFORM_PATH=target/debug` so that `cargo build` output is found automatically without copying DLLs into `platforms/`.

### 8.11.6 Standard Library Structure (Reference Implementation)

There is no language-level requirement for the standard library structure.

## 8.12 Macro Interaction [Tested tests/ring2::neg_private_macro_not_importable, tests/macros::batch_defmacro_simple]

### 8.12.1 Pre-Expansion Processing

The `mod`, `import`, and `export` forms MUST be extracted from raw S-expressions before macro expansion. They are NOT subject to macro expansion.

### 8.12.2 Cross-Module Macro Availability

Macros from imported modules are available for expansion in the importing module. Since modules compile in topological order, a macro's compiled expansion function is available by the time any importer needs it.

### 8.12.3 Macro Hygiene

Macro authors SHOULD use qualified names for non-prelude references within macro bodies to avoid capture by the importing module's local names.

## 8.13 REPL Integration [R4 S10]

A conforming REPL implementation SHOULD support the following module-related behaviors.

### 8.13.1 Default Module

The REPL starts in a default `user` module. The prelude is auto-imported, providing all standard library names as bare symbols.

### 8.13.2 Module Switching

The REPL SHOULD support switching between modules (the mechanism is implementation-defined). When switching to a different module, the set of available bare names changes to reflect that module's definitions and imports.

```
user> (defn greet [name] (str-concat "Hello " name))
user> /mod math
math> greet                    ; Unknown symbol
math> user/greet               ; (fn [String] String) -- qualified access works
math> /mod user
user> greet                    ; (fn [String] String) -- still defined
```

### 8.13.3 Interactive Import

The REPL SHOULD support `(import ...)` as an interactive command. Importing a module at the REPL loads it on demand (if not already loaded) and installs its names into the current module's scope.

### 8.13.4 Module Self-Documentation

Typing a module name at the REPL SHOULD display information about that module: its public definitions, types, and traits. This is consistent with the self-documenting design principle.

## 8.14 Summary of Forms [Tested]

| Form | Purpose | Visibility |
|---|---|---|
| `(mod name)` | Declare public submodule | Public |
| `(mod name forms...)` | Declare inline submodule (extracted to file) | Public |
| `(mod- name)` | Declare private submodule | Private |
| `(import [mod [names]])` | Import names into current scope | N/A |
| `(import [super [*]])` | Import from parent module | N/A |
| `(export [mod [names]])` | Re-export names as public API | Public |
| `module/name` | Qualified name reference | N/A |
| `Type.member` | Dotted member access | N/A |

## 8.15 Complete Example [R4 S10]

The following example demonstrates the full module system in a project with multiple files, imports, exports, visibility, and qualified access.

```
project/
  main.cl
  shapes.cl
  shapes/
    display.cl
```

```clojure
;; shapes.cl
(mod display)

(deftype Shape
  (Circle [:Float radius])
  (Rect [:Float width :Float height]))

(defn- validate [:Float x] :Bool (> x 0.0))

(defn circle [:Float r] :Shape
  (Circle r))

(defn rect [:Float w :Float h] :Shape
  (Rect w h))
```

```clojure
;; shapes/display.cl
(import [primitives [*]])

(impl Display Shape
  (defn show [self]
    (match self
      [(Circle r) (str-concat "Circle(" (str-concat (show r) ")"))
       (Rect w h) (str-concat "Rect(" (str-concat (show w)
                    (str-concat "x" (str-concat (show h) ")"))))])))
```

```clojure
;; main.cl
(mod shapes)
(platform stdio)
(import [shapes   [circle rect Shape Circle Rect]
         platform.stdio [*]])

(defn main []
  (do
    (print (show (circle 2.5)))         ; uses imported 'circle' and 'show'
    (print (show (rect 3.0 4.0)))       ; uses imported 'rect'
    (print (show (shapes/circle 1.0)))  ; qualified access also works
    ))
```
