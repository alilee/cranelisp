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

Module identity is determined solely by the file's path relative to the project root. A `(mod name)` declaration does **not** rename the loaded module — it triggers loading of the file at the resolved nested path, and that file's module identity is the path of the file itself. If `main.cl` contains `(mod util)`, the search (Section 8.2.5) resolves to the nested child `main/util.cl`, so the loaded module is named `main.util` — never a sibling `util.cl` at the project root (that file, if present, is the independent peer module `util`, reachable only via `import`, not `mod`).

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

## 8.2 Module Declaration [Tested tests/spec_08_modules::mod_test_child_in_trait_module_does_not_redefine_parent_trait]

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

### 8.2.3 Private Submodule Declaration [Tested+Neg tests/spec_08_modules::mod_dash_private_submodule_not_importable_from_peer_neg]

```clojure
(mod- internal)
```

Declares `internal` as a private submodule, accessible only within the declaring module and its submodule subtree. Other modules MUST NOT import from or reference names in a private submodule.

### 8.2.5 File Resolution [Tested tests/spec_08_modules::bare_mod_decl_resolves_nested_child_for_entry_main]

When `(mod name)` appears in a file (after inline extraction, if applicable), the implementation MUST resolve the corresponding `.cl` file to the child directory path only:

- **Child directory**: `{parent_dir}/{stem}/{name}.cl` -- where `{stem}` is the declaring file's name without extension.

For example, if `app.cl` contains `(mod handler)`, the implementation resolves to `app/handler.cl`. If this file does not exist, it is a compile-time error.

Sibling files (e.g., `handler.cl` in the same directory as `app.cl`) are NOT considered. A sibling file is a peer module, not a submodule. Allowing sibling fallback would create ambiguity: the same file could be both `app.handler` (via `mod`) and root module `handler` (via the search path in §8.11.2), violating §8.1's principle that file path determines module identity. To reference a peer module, use `import` with the module's own name (e.g., `(import [handler [...]])`), not `mod`.

### 8.2.6 Placement [Tested crates/cranelisp-frontend/src/module_extract.rs::test_mixed_forms]

`mod` declarations MUST appear as top-level forms. They are extracted from the raw S-expression stream before macro expansion. A `mod` form encountered in any other position (inside a function body, let binding, etc.) is an error.

**Example -- multi-module project:**

The entry file `main.cl` declares two submodules. Per §8.2.5, each `(mod name)` resolves to the nested child path `{stem}/{name}.cl` — so `main.cl`'s `(mod util)` loads `main/util.cl` (module `main.util`) and `(mod math)` loads `main/math.cl` (module `main.math`). The submodules live in the `main/` directory beside the entry file, NOT as siblings of `main.cl`:

```
project/
  main.cl             ; root module (entry point)
  main/
    util.cl           ; module "main.util"
    math.cl           ; module "main.math"
```

```clojure
;; main.cl (entry point)
(mod util)
(mod math)

(defn main []
  (print (show (main.util/helper 42))))
```

```clojure
;; main/util.cl  -> module "main.util"
(defn helper [:Int x] :Int (+ x 1))
```

```clojure
;; main/math.cl  -> module "main.math"
(defn double [:Int x] :Int (* x 2))
```

## 8.3 Import [Tested tests/spec_08_modules::import_specific_name_compiles_and_runs]

The `import` special form brings names from other modules into the current module's scope as bare (unqualified) symbols.

```ebnf
import_form  = '(' 'import' '[' import_entry+ ']' ')'
import_entry = module_spec names_list
module_spec  = symbol                            ; bare module path
             | 'super'                           ; parent module reference
             | '(' symbol symbol ')'             ; (module alias) pair
names_list   = '[' name+ ']'                     ; specific names (each entry independently classified)
             | '[' '*' ']'                        ; all public names from the source module
             | '[' member_glob ']'                ; all members of a type or trait
             | '[' ']'                            ; no names (alias-only or null import)
name         = symbol                            ; bare import — local name = source export name
             | dotted_symbol                     ; selective member import (per §1.4.4 lexical)
             | '(' symbol symbol ')'             ; renamed bare import — (source-name local-name)
             | '(' dotted_symbol symbol ')'      ; renamed selective member — (Type.SourceMember local-name)
member_glob  = symbol '.*'                       ; e.g. Display.*
```

### 8.3.1 Specific Name Import [Tested+Neg crates/cranelisp-frontend/src/module_extract.rs::test_import_specific_names, tests/spec_08_modules::import_of_non_existent_name_errors_neg]

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

### 8.3.5 Renamed Import

```clojure
(import [core.option [(Some Maybe-Just) None]])
```

Imports `Some` from `core.option` as the local bare name `Maybe-Just`; imports `None` unchanged. The local symbol-table entry for `Maybe-Just` is `ModuleEntry::Import { source: core.option/Some }` — the rename is a local-name aliasing layered on top of the standard import resolution. Per §8.6.2, lookups follow the source chain transitively.

Renamed selective members:

```clojure
(import [core.option [(Option.Some Just)]])
```

Imports the selective member `Option.Some` as local bare `Just`. The same dotted-vs-bare classification per §8.3.11 applies — `Option` is NOT brought into scope via this entry; only `Just` is.

The accessibility-matrix entries from §8.3.11 extend naturally to renamed forms — substitute the local name everywhere the source name appears.

A rename of a symbol to itself (e.g. `[(Some Some)]`) MUST NOT be rejected; it is redundant but valid. An implementation MAY emit a style warning.

Per §8.6.4, two import entries that produce the SAME local name (whether via rename or bare) are a duplicate-name conflict and MUST produce a compile-time error.

**Composition with aliases.** Renamed forms compose with module aliases (§8.3.4):

```clojure
(import [(core.string str) [(concat join-strings) chars]])
```

Imports `concat` as local `join-strings`, imports `chars` unchanged, AND registers `str` as a local module alias for `core.string`.

**Negative cases** (compile-time errors):

- `(import [m [(Some X) (None X)]])` MUST be a compile-time error — duplicate local name `X` within a single import entry.
- `(import [m [(Some X)] n [Y X]])` MUST be a compile-time error if `X` is bound twice across import entries (per §8.6.4).
- After `(import [m [(Option.None X)]])`, writing `:Option` MUST be a compile-time error — the parent type `Option` is NOT in bare scope (only local `X` is).

### 8.3.6 Alias-Only Import

```clojure
(import [(core.option opt) []])
```

Registers `opt` as an alias for `core.option` without importing any bare names. Useful when you only want qualified access: `opt/Some`.

### 8.3.7 Null Import

```clojure
(import [core.option []])
```

Imports nothing and does not trigger module loading or resolution. Useful to suppress the implicit prelude import (§8.8.1) — an explicit `(import [prelude []])` replaces the implicit glob without loading the prelude module.

### 8.3.8 Super Import [Tested+Neg tests/spec_08_modules::super_import_resolves_parent_fn]

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

> **Known limitation — mutual-import deadlock.** `super` is supported for one-directional child → parent imports. If the parent module imports anything (directly or transitively) from a child that uses `(import [super ...])`, the compiler's form-by-form scheduler deadlocks during typechecking: the parent blocks on the child's signatures while the child (via `super`) blocks on the parent's. A conforming implementation MAY reject this configuration with a diagnostic, but MUST NOT silently produce a non-terminating compilation. Authors SHOULD NOT construct parent↔child mutual-import cycles. Test submodules that need to enumerate their parent's symbols SHOULD use the `discover-tests` primitive (import-required; see [Appendix A.3](appendix-a-builtins.md#test-discovery-and-error-capture)) — it observes the parent's symbol table at runtime, returning late-bound callables, without requiring a `super` import, avoiding the deadlock entirely. Running a discovered test is simply invoking its callable (optionally bracketed by `catch-runtime-error`); there is no separate `run-test` builtin. See `design/arch/CLAUDE.md` Decision 30 for the underlying pass-order constraint. A future language version may redesign the module-loading pass order to lift this restriction; no timeline is promised.

### 8.3.9 Multiple Module Import

Multiple modules MAY be imported in a single `import` form:

```clojure
(import [core.option [Some None]
         core.math   [*]
         core.fmt    [Display.*]])
```

Module-names-list pairs are processed left to right.

### 8.3.10 Placement [Tested+Neg tests/spec_08_modules::import_below_use_still_available_before_definitions, tests/spec_08_modules::import_inside_let_rejected_neg]

`import` forms MUST appear as top-level forms. They are extracted from the raw S-expression stream before macro expansion. An implementation MUST process `import` before compiling definitions in the same module, so that imported names are available during type checking and code generation.

A module MAY contain multiple `import` forms. Their effects accumulate: names imported by each form are merged into the module's symbol table. The conflict rules in Section 8.6.4 apply across all `import` forms — importing the same bare name from two different source modules (across any number of `import` forms) is an error.

**Example -- importing types and constructors:**

```clojure
;; main.cl
(mod types)                                    ; resolves to main/types.cl (module main.types)
(import [main.types [Point make-point x y]])

(defn main []
  (let [p (make-point 3 4)]
    (print (show (x p)))))
```

```clojure
;; main/types.cl  -> module "main.types"
(deftype Point [:Int x :Int y])
(defn make-point [:Int x :Int y] :Point (Point x y))
```

### 8.3.11 Accessibility After Import [Tested+Neg]

Each entry in an import name list independently affects what is in bare scope after the import resolves. The following base cases enumerate the effects for an import from a module that exports a type `Option` with constructors `Some` and `None`. Multi-entry name lists union their effects (see §8.3.10 for accumulation rules across forms; the same rules apply within a single name list).

**Bare-scope effects:**

| Name-list entry | Bare scope after | `:Type` annotation accessible |
|---|---|---|
| `Option` (bare symbol matching a top-level export) | `Option` (the type name) | `:Option` works (Option is a type) |
| `Option.None` (dotted symbol — selective member) | `None` only | NO — `Option` is not brought into bare scope |
| `Option.*` (member glob) | all members of Option as bare names (`Some`, `None`) | NO — `Option` is not brought into bare scope |
| `*` (glob — all public names) | every public export of the source module brought as bare names — including `Option`, `Some`, `None` if all are public | YES — `Option` is in bare scope via the glob |

A conforming implementation MUST classify each name-list entry independently per the table above. An entry of the form `Symbol` MUST bring only the top-level export `Symbol` into bare scope. An entry of the form `Symbol.member` MUST bring only `member` into bare scope and MUST NOT bring `Symbol` into bare scope. An entry of the form `Symbol.*` MUST bring all public members of `Symbol` into bare scope and MUST NOT bring `Symbol` itself into bare scope. The `*` glob entry MUST bring every public name of the source module into bare scope.

**Derived dotted access** (per §8.5.2): wherever a type or trait is in bare scope, dotted access to its members works automatically. `Option.Some` and `Option.None` are accessible as dotted references in any scope where `Option` is bound — whether imported as `[Option]`, brought in via `[*]`, defined in the current module, or referenced via a qualified name. Dotted access is **not a separate import target**; it is a consequence of the parent type or trait being in bare scope.

**Composition example:** `(import [m [Option Option.*]])` brings `Option`, `Some`, and `None` as bare names — equivalent to `(import [m [*]])` for a module exporting only `Option`. `(import [m [Option Some]])` brings `Option` and `Some` (but not `None`).

**Negative cases** (compile-time errors):

- After `(import [m [Option.None]])`, writing `:Option` MUST be a compile-time error: the type `Option` is not in bare scope.
- After `(import [m [Option.None]])`, writing `Option.Some` as a dotted reference MUST be a compile-time error: the parent type `Option` is not in bare scope.
- After `(import [m [Option.*]])`, writing `:Option` MUST be a compile-time error (same reason).
- After `(import [m [Option.*]])`, writing `Option.Some` as a dotted reference MUST be a compile-time error (same reason).
- After `(import [m [Option]])` (with no explicit member import), writing bare `Some` MUST be a compile-time error unless `Some` is brought in by another import or defined locally.
- Multi-entry composition: `(import [m [Option Option.*]])` MUST NOT be an error; the effects union without conflict (Option as type + members as bare names, no duplicate-bare-name).

**Renames in the accessibility matrix.** For any entry of the form `(source-name local-name)` (per §8.3.5), the resulting bare scope contains `local-name` (not `source-name`); the resolution chain points at the source. Accessibility-after-import substitutes the local name everywhere the source name appears in the base matrix above.

Examples:

- `(import [m [(Option O)]])` — `O` (type alias for `Option`) in bare scope; `:O` works as type annotation; `O.Some` and `O.None` work as dotted refs (the type `Option` is reachable through `O` via the rename).
- `(import [m [(Option.None NoneAlias)]])` — `NoneAlias` in bare scope; `Option` NOT in scope; `:Option` MUST NOT resolve.
- `(import [m [(Option O) Option.*]])` — `O` plus bare `Some`, `None` (members of `Option` as bare names; the parent name is reachable via the rename `O`).

The same rules apply symmetrically when consumers import from a renamed re-export — they see the renamed local name in this module's public API (per §8.4.5).

See §8.6.4 for the general conflict rules and §8.6.5 for the ambiguity resolution discipline.

## 8.4 Export [Tested crates/cranelisp-frontend/src/module_extract.rs::test_export_specific, crates/cranelisp-frontend/src/module_extract.rs::test_export_glob]

The `export` special form re-exports names from imported modules, making them part of the current module's public API.

```ebnf
export_form  = '(' 'export' '[' export_entry+ ']' ')'
export_entry = module_spec names_list      ; same module_spec and names_list as §8.3
```

The full §8.3 grammar (`module_spec` including the `(module alias)` pair form; `names_list` including the symbol-rename forms `(symbol symbol)` and `(dotted_symbol symbol)`) applies symmetrically to exports. Anywhere an import may rename a name or alias a module, an export may do the same.

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

### 8.4.4 Module Mounting on Export

```clojure
(export [(core.string str) [concat join]])
```

This form does two things:

1. Re-exports `concat` and `join` as bare names in the current module's public API (semantically equivalent to `(export [core.string [concat join]])`).
2. **Mounts** `core.string` at the dotted module-path `current-module.str` — every public name in `core.string` becomes reachable through the current module's namespace as a qualified reference `current-module.str/<name>`. The mount is **full and transparent**: downstream consumers MAY reach ANY public name of `core.string` via the alias, not only the re-exported subset.

Note the form of the alias: per §1.4.3, a qualified name contains exactly one `/` separating `module_path` from `local_name`, and `module_path` is dot-separated. The mount adds `str` as a new segment within the current module's `module_path`, NOT as a separate `/`-delimited component. There is no two-slash notation in Cranelisp.

Downstream consumers — modules that import from the current module — MAY write:

```clojure
(import [current-module.str [split chars]])   ; resolves split, chars from core.string via the mount
(current-module.str/upper "x")                ; qualified ref through the mount
```

The mount is functionally a public module-path alias. An implementation MUST track it so that qualified-name resolution per §8.6.6 walks the alias chain to the underlying source module.

**Worked example — resolution of a mount-aliased qualified name.** Given:

```clojure
;; Module A has (export [(core.string str) [concat]])
;; — mounts core.string at A.str

(A.str/split "hello,world" ",")
```

Resolution proceeds as follows:

1. Parser sees `A.str/split` as `qualified_name` (per §1.4.3) with `module_path = A.str` (segments: `A`, `str`) and `local_name = split`.
2. Resolver tries `lookup_module(A.str)` — miss (`A.str` is not a stored module path).
3. Walk back the dot-separated segments: try `lookup_module(A)` — hit (`A` is a known module).
4. Check `A`'s alias table for the next unmatched segment `str` — found, public mount alias to `core.string`.
5. Substitute: the matched segment `str` is replaced by the alias's target, so `module_path` becomes `core.string`.
6. Restart resolution: `lookup_module(core.string)` — hit.
7. Look up `split` in `core.string`'s public symbol table — hit. Resolution complete.

**Mount-only export** (analogous to §8.3.6 Alias-Only Import):

```clojure
(export [(core.string str) []])
```

Mounts `core.string` at `current-module.str` WITHOUT re-exporting any names as bare. Useful when the bare-name pollution is undesired but the mount is wanted.

A bare-form mount without an alias (e.g. `(export [m []])`) re-exports no names and registers no mount. An implementation MAY treat this as a no-op or MAY reject it as a vacuous declaration; either is conforming.

**Negative cases** (compile-time errors):

- Two export forms mounting different source modules at the same alias path MUST be a compile-time error: `(export [(core.string foo) [...]] [(core.option foo) [...]])` MUST be rejected — duplicate mount alias `foo` (per §8.6.4).
- An export mount whose alias collides with an actual submodule of the current module MUST be a compile-time error: if module `A` declares `(mod inner)` AND `(export [(other.mod inner) [...]])`, that combination MUST be rejected — `A/inner` would be ambiguous.

### 8.4.5 Renamed Re-Export

```clojure
(export [core.option [(Some Just) None]])
```

Re-exports `Some` from `core.option` as `Just` in the current module's public API; re-exports `None` unchanged. The current module's symbol-table entry for `Just` is `ModuleEntry::Reexport { source: core.option/Some }`. Downstream consumers see `Just` in this module's public API and reach `core.option/Some` via chain-follow per §8.6.2.

Renamed selective members:

```clojure
(export [core.option [(Option.Some MaybeJust)]])
```

**Composed forms (renaming + mounting):**

```clojure
(export [(core.option opt) [(Some Just) None]])
```

- Re-exports `Some` from `core.option` as `Just`.
- Re-exports `None` from `core.option` unchanged.
- Mounts `core.option` at the dotted module-path `current-module.opt` — full transparent.
- Note: `current-module.opt/Some` (the ORIGINAL name) resolves via the mount, even though the bare name in this module is `Just`. The bare name and the mounted qualified path are independent surfaces over the same underlying source.

This is the canonical pattern for "rename for bare-name ergonomics, but preserve qualified-path access for explicit callers."

A rename of a symbol to itself in an export (e.g. `[(Some Some)]`) MUST NOT be rejected; it is redundant but valid.

**Negative cases** (compile-time errors):

- `(export [m [(Some X) (None X)]])` MUST be a compile-time error — duplicate exported name `X` (per §8.6.4).
- Cross-entry collision: `(export [m [(Some X)] n [X])` MUST be a compile-time error if `X` would be bound by two distinct sources.

### 8.4.6 Semantics

A re-exported name becomes a public name of the exporting module. When another module imports from the exporting module (via `[*]` or by name), re-exported names are included.

An implementation MUST track re-export provenance so that introspection can display the original defining module, not the re-exporting module. For example, if `prelude` re-exports `print` from `platform.stdio`, introspection SHOULD display `platform.stdio/print` as the origin.

### 8.4.7 Placement

`export` forms MUST appear as top-level forms. They are extracted alongside `mod` and `import` before macro expansion.

### 8.4.8 Implicit Impl Re-export [S66]

Trait implementations are NOT enumerable in `export` (or `import`) lists. An impl form `(impl Trait Type ...)` does not have a name that can appear inside `[...]`. Instead, **re-exporting a trait or a type implicitly re-exports any impl whose trait + type are reachable through the re-exporter's import closure**.

Concretely: if module M re-exports a trait `T` (via `(export [src [T ...]])` or `(export [src [*]])`), then any `(impl T Type)` reachable from M — declared in M itself or in any module M transitively imports — is visible to a module that imports `T` from M, provided the importer also reaches `Type`. The same rule applies symmetrically to re-exporting a type: any `(impl Trait Type)` impl reachable from M comes along for the ride wherever `Type` reaches.

This avoids forcing authors to enumerate impls in re-export lists — a list that has no syntactic anchor to enumerate against, since impls are nameless. Users see the rule as: **impls follow their trait and type through the import graph.**

See [§5.11.1](05-definitions.md#5111-impl-visibility--transitive-import-closure) for the full visibility statement (which §8.4.8 is the module-side projection of) and a worked three-module example, and [§7.11.1](07-traits.md#7111-impl-visibility--transitive-import-closure) for the trait-resolution consequences.

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

## 8.5 Qualified Names [Tested tests/spec_08_modules::qualified_name_resolution]

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

Qualified-name resolution per §8.6.6 walks module alias chains. Alias substitution operates on the dot-separated segments of `module_path` (within the grammar above), NOT across `/`. If the current resolution scope contains a public mount alias under module `current-module` that maps the segment `str` to `core.string` (per §8.4.4), then writing `current-module.str/split` causes the resolver to walk `module_path` segment-by-segment: it finds `current-module`, looks up `str` in that module's alias table, substitutes `core.string`, and then resolves `split` in `core.string`. Mount aliases declared by `export` are public; alias-imports declared by `import` (§8.3.4) are private to the importing module.

### 8.5.2 Dotted Names [Tested tests/spec_field_accessor::cross_module_canonical_accessor_resolves, tests/spec_field_accessor::cross_module_contested_canonical_accessors_no_cliff, tests/spec_field_accessor::list_shows_canonical_qualified_accessor, tests/spec_05_definitions::type_member_field_accessor_disambiguates_poisoned_field, tests/spec_05_definitions::type_member_accessor_typed_fn_of_type]

The `.` within a name provides access to members of types and traits. A member is a **constructor** of the type, a **field accessor** of the type, or a **method** of the trait:

```clojure
Option.Some             ; constructor 'Some' of type 'Option'
Option.None             ; constructor 'None' of type 'Option'
Box.v                   ; field accessor 'v' of type 'Box'  (see §5.2.6)
Display.show            ; method 'show' of trait 'Display'
Num.+                   ; operator '+' of trait 'Num'
```

Dotted names resolve directly from the parent type or trait definition, bypassing the bare-name lookup. This means they work even when the bare name is ambiguous (see Section 8.6.5).

**Field-accessor members are the CANONICAL accessor name (FIXME 0365/0439).** When `member` names a field accessor generated by `Type` (§5.2.6), `Type.member` is the **canonical, primary** accessor reference, typed `(Fn [Type] FieldType)` — `Box.v` is the real name of `Box`'s `v` accessor, just as `Option.Some` is the real name of the `Some` constructor. The **bare** field name (`v`) is a convenience *alias* to this canonical form (§5.2.6), available when exactly one in-scope type owns the field; the dotted form is not a fallback reached only under contention — it is the accessor's name, always valid. Given `(deftype Box [:Int v])` and `(deftype Cup [:Bool v])`, `Box.v` resolves to `(Fn [Box] Int)` and `Cup.v` to `(Fn [Cup] Bool)` directly and unconditionally; the contest (if any) is over the single bare alias `v`, not over these canonical accessors. Like dotted constructor/method access, the canonical accessor is a derived consequence of `Type` being in bare scope (no separate import) and is first-class — `Box.v` MAY be passed as an argument or bound to a variable.

`Type.member` always denotes exactly one thing — a field accessor never has to be disambiguated against a same-named trait method: a trait `impl` whose method name collides with an existing field-accessor name of the target type is **rejected at impl time** (§7.3.1, FIXME 0365). Constructors are uppercase and accessors/methods are lowercase, so the only possible same-name collision is accessor-vs-method, and that collision is prevented at the definition site — leaving the canonical `Type.member` a unique referent in every case.

**Canonical display form.** Because `Type.field` is the canonical accessor name, it is the form the language uses when it **displays or reports** an accessor (consistent with the qualified-display convention applied to all names — `:primitives/Int`, `:(Fn [a] a) user/id`). The bare alias is a convenience for source input, but introspection and reporting name the accessor by its canonical `Type.field`. (The exact wording of any REPL command surface that lists accessors is the REPL experience spec's concern, not specified here.)

Dotted access is **derived** from the parent type or trait being in bare scope, not from a separate import. Whenever `Option` is bound in the current scope (via import, current-module definition, or qualified reference), `Option.Some` and `Option.None` are accessible as dotted references with no additional import statement required. Per §8.6.5, the dotted form is also the canonical disambiguator when bare `Some` is poisoned by simultaneous imports from multiple sources. In valid (non-ambiguous) code, bare names suffice and dotted forms are rarely needed.

### 8.5.3 Combined Qualification

Module path and dot notation MAY be combined:

```clojure
core.option/Option.Some     ; fully qualified constructor
core.fmt/Display.show       ; fully qualified trait method
```

### 8.5.4 Auto-Loading

When a qualified name references a module that has not yet been loaded, the implementation SHOULD attempt to load that module on demand. This enables qualified references to work without explicit `import` or `mod` declarations.

In a REPL environment, qualified name references SHOULD trigger lazy loading of the referenced module.

A qualified name MAY resolve to any kind of symbol, including a **macro**. When the resolved symbol is a macro, the compiler invokes its expansion at the qualified call site, just as for a bare-name macro. Lazy loading applies equally: a qualified macro reference MAY trigger registration and typechecking-and-compilation of its defining module (see §9.3.6 for the macro-specific mechanics).

## 8.6 Name Resolution [Tested tests/spec_08_modules::local_let_shadows_imported_name]

Name resolution converts source-level names into their definitions. An implementation MUST follow the resolution layers defined in this section.

### 8.6.1 Resolution Layers

Resolution proceeds through three layers, in order:

1. **Local environment**: `let` bindings, `fn` parameters, and `match` pattern variables. These are lexically scoped -- pushed on entry to a binding form and popped on exit.

2. **Module scope**: Definitions within the current module, plus names brought in via `import`. This layer consults the current module's symbol table (the **inner scope**), following `Import` and `Reexport` references to their source modules. When the inner scope misses and the module receives the implicit prelude (§8.8.1), this layer falls back to the prelude's public bindings (the **outer scope**, per §8.6.4) before proceeding to the root module. Within the inner scope there is **no def-over-import precedence tier**: a module-local definition and an explicit import are peers, and their contesting the same bare name is a **conflict** per §8.6.4 (definition-over-import), not a shadow. Only the inner-vs-outer boundary is a shadowing relation (local definitions and explicit imports shadow prelude-fallback names, §8.6.4).

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

- **Definition over import** `[S102]`: A definition (`defn`, `deftype`, etc.) in the current module that has the same name as an explicitly imported name:

  ```clojure
  (import [math [add]])
  (defn add [x y] (+ x y))           ; error: definition conflicts with import
  ```

  This conflict is order-independent and applies in every mode, including forms entered interactively at the REPL — see §"Definition-Over-Import: Order-Independent, All Modes" below for the full pinned statement.

- **Rename collisions**: Two import (or export) entries — whether via rename or bare — producing the same local (or exported) name MUST produce a compile-time error. Example: `(import [m [(Some X) (None X)]])` is an error — duplicate local name `X`.

- **Mount collisions**: Two export forms mounting different source modules at the same alias path MUST produce a compile-time error. Example: `(export [(core.string foo) [...]] [(core.option foo) [...]])` is an error — duplicate mount alias `foo`.

- **Mount-vs-submodule collisions**: An export mount whose alias collides with an actual submodule `(mod inner)` of the current module MUST produce a compile-time error. Example: if module `A` declares `(mod inner)` AND `(export [(other.mod inner) [...]])`, that's an error — `A/inner` would be ambiguous.

Same-source duplicates (the same name arriving through two re-export paths from the same original definition) are NOT ambiguous. The comparison is by **terminal source**, not immediate source: before declaring a same-name collision, an implementation MUST chain-follow BOTH import/re-export edges (per §8.6.2) to their terminal `(home_module, canonical_symbol)` — the original `Def` at the end of each chain. If the two terminals are equal, the imports denote the same original definition and dedup silently (no error); only **distinct** terminals collide. [Tested+Neg tests/spec_08_modules::glob_and_reexport_of_same_terminal_dedup, tests/spec_08_modules::distinct_terminal_overlap_collides]

This terminal-source comparison is what makes a glob `(import [primitives [*]])` co-exist with a specific `(import [m [Option]])` when `m` re-exports `primitives/Option`: both bare `Option` entries chain-follow to the same terminal `primitives/Option`, so they dedup rather than poisoning the name. Comparing only the **immediate** source module (`primitives` vs `m`) would wrongly read these as two sources and report a false collision. The same rule resolves the common real-world shape "glob a module AND specifically import a name it re-exports."

#### Explicit Imports Shadow the Implicit Prelude [S20]

The implicit prelude is an **outer scope**, not a set of bindings materialised into the module's symbol table. A module's own symbol table is its **inner scope**: it holds only the module's local definitions and its *explicit* imports/re-exports. The implicit prelude (injected per §8.8) is a separate **outer scope** — the `prelude` module's own public bindings — consulted **only on a resolution miss in the inner scope**. Prelude bindings are NOT copied into the module's table.

Because resolution consults the inner scope before falling back to the outer prelude scope, explicit imports and local definitions shadow prelude-provided names automatically — without producing a duplicate-import error. The shadow is a lookup ordering (inner before outer), not a same-table override. This is exactly the scope layering the resolution layers in §8.6.1 describe: explicit imports take precedence over the implicit prelude, just as inner `let` bindings shadow outer ones.

The conflict rules above (duplicate imports, definition-over-import, rename/mount collisions, and the §8.6.5 ambiguity poisoning) operate over the **inner scope only** — the module's local definitions and its explicit imports. The implicit-prelude outer scope never participates in these checks: a name an explicit import (or a local definition) provides does not collide with a same-named prelude binding, because the prelude binding is not in the inner table. Two *explicit* entries that produce the same local name remain a conflict exactly as before.

When an explicit glob import brings in a name that the prelude would also provide, the explicit version (in the inner scope) is found first, and the prelude's binding is simply never consulted for that bare name. This means the module loses bare-name access to the prelude's binding. Remediation strategies:

- **Qualified access**: Use `prelude/Some` or `primitives/Some` to reach the shadowed name.
- **Selective import**: Replace `(import [grid [*]])` with `(import [grid [solve other-fn]])` to avoid importing names that collide.
- **Explicit prelude re-import**: Add `(import [prelude [Some None]])` after the glob import to restore specific prelude names.

**Practical note**: Glob imports from modules with large public APIs can silently displace prelude bindings (e.g., a module that re-exports `Some`/`None` for convenience). When debugging unexpected type errors after adding a glob import, check whether prelude names have been shadowed.

#### Definition-Over-Import: Order-Independent, All Modes [S102]

Arbitrated S102 (FIXME 0484). The definition-over-import conflict above is pinned as follows.

**Framing — a collision is not resolved by importing; the resolution is the fully-qualified reference.** Creating a symbol (a definition in the current module) whose name collides with a name that an import brought into scope is **not** an import-resolution question — there is no shadowing, no precedence, and no "which import wins." It is a **compile-time error**. The mechanism the language offers for reaching a *different* module's same-named symbol is the **fully-qualified reference** (`module/name`, §8.6.6): a module owns its own public `foo`, and to reach another module's `foo` it writes `other/foo`. The two `foo`s never share a bare binding, so there is nothing to disambiguate. This rests on the nominal-typing property (§3.8.4): same-named types/values from different modules are genuinely distinct, so the fully-qualified name denotes exactly one of them. A definition that collides with an import is telling the compiler two incompatible things about one bare name; the remedy is to stop importing the name you define and fully-qualify the reference to the other module's symbol where it was used.

**A definition form (`defn`, `def`, `deftype`, `deftrait`, `defmacro`, and their private `-` variants) whose name is already bound in the current module's inner scope by an explicit import — specific, renamed, member, or glob — MUST be rejected with a compile-time error.** The rejected form has no effect on the module: the bare name continues to resolve to the import, and introspection MUST continue to describe the imported definition. A local definition is always a fresh terminal source, so the terminal-source dedup above can never reconcile it with the import — the collision is unconditional.

**Uniform across glob and specific imports — there is NO glob-exemption.** The rule bites identically whether the colliding imported name arrived via a specific import (`(import [m [name]])`), a renamed or member import, a glob import (`(import [m [*]])`), or a glob **re-export** (`(export [m [*]])`, which populates the inner scope per §8.6.2). A glob is a convenience for pulling in the *non-colliding* names of a module; it does not license silently redefining one of the names it would have brought in. A name you define is yours, and if a glob would also have supplied that name, defining it is the collision this section rejects — not a permitted shadow. *(An earlier S102 draft floated exempting glob imports from the error — the "glob-of-seeded-ADT-constructors" prelude pattern — so that a glob-brought name could be silently redefined. That draft is **superseded**: there is no glob-exemption. A module that both glob-imports a source and defines one of that source's names must instead fully-qualify its references to the colliding source symbol rather than importing a name it defines — see the stdlib-hygiene consequence below.)*

The rule is:

- **Order-independent.** Whether the imported name was *used* before the conflicting definition appears MUST NOT affect the outcome. Name resolution is a property of the module's binding set, never of call history. There is no normative pre-shadow/post-shadow distinction: an implementation in which an already-exercised import behaves differently from an unexercised one under a same-name definition is defective on both legs — the definition must be rejected in both.

- **Uniform across modes.** The rule applies identically to batch compilation (`--run`, `--link`) and to forms entered interactively at the REPL. In interactive mode, the **later-arriving form is the rejected one**: a definition entered over an existing explicit import fails, and symmetrically, an `import` entry that would bind a bare name already bound by a module-local definition fails; in both cases the pre-existing binding and the rest of the session state are unchanged. A REPL session MUST NOT accept a binding set that its own regenerated backing file would reject when batch-compiled — an interactive definition-over-import shadow would produce a module source containing both the import and the definition, which this section rejects, breaking session/file round-trip.

```
user> (import [util [measure]])
user> (measure [1 2 3])
:primitives/Int 3
user> (defn measure "user shadow" [v] :Int 99)
error: definition of 'measure' conflicts with the explicit import from 'util'
       (rename the definition, use a renamed import (§8.3.5), or drop
       'measure' from the import list)
user> (measure [1 2 3])
:primitives/Int 3                    ; the import remains the binding
```

The transcript is identical with or without the pre-definition call to `(measure ...)` — the definition is rejected either way.

**Contrast — prelude-provided names remain shadowable.** A module-local definition over a name that reaches the module only through the implicit-prelude fallback (the outer scope, §8.8.1) is NOT a conflict: the inner-scope definition shadows the outer scope structurally, per §"Explicit Imports Shadow the Implicit Prelude" above. Redefining `count` is permitted when `count` arrives via the prelude; it is an error when the module *explicitly imported* `count`. The distinction is intent: an explicit import is the author's statement "this module's `count` is `collections.vec/count`", which a same-name local definition contradicts rather than refines — whereas prelude names are ambient convenience the author never asked for by name. (Clojure draws the same line: defining over a `:refer`ed name is an error; defining over a `clojure.core`-provided name — the prelude analogue — is a permitted shadow.)

**Rationale.**

1. **No silent winner.** §8.6.5 pins that two distinct terminal sources contesting one bare name MUST error rather than one silently winning ("glob imports are peers of specific imports"). A local definition versus an explicit import is exactly such a contest; resolving it silently in either direction is the footgun this section exists to prevent.
2. **Round-trip validity.** The REPL `user` module persists to a backing file and must batch-compile. Any interactive precedence other than rejection would admit sessions whose regenerated source is an invalid module.
3. **The nearest-scope precedent does not apply.** §8.11.2.1 (S98, submodule-first) orders *search tiers* for bare **module** names, where the losing candidate remains independently reachable by its own path. Here two bindings contest a single inner-scope name slot — §8.6.4/§8.6.5 conflict territory, not search-order territory. The analogous nearest-scope shadow in name resolution is layer 1 (`let`/`fn` bindings, §8.6.3) and the inner-over-outer prelude shadow — both scope *layerings*, not same-layer collisions.

**Diagnostics.** The error SHOULD name the import's source module and offer remediations: rename the local definition; convert the import to a renamed import (§8.3.5) to move it out of the way; drop the name from the import list (using a qualified reference where the import was used); or suppress the import entirely. Whether a REPL additionally offers an affordance to *remove* an import binding from a live session (so the name can then be defined) is a REPL-experience concern (`repl/spec.md`), not specified here.

**Implementation consequence (informative — for the binary/orchestration surface).** The rejection fires when a staged definition's name matches a name that an active import (specific, renamed, member, glob, or glob re-export) has brought into the module's inner scope. Whether the arriving form is a glob or a specific import — the distinction the superseded draft leaned on — is available at import/definition-processing time (the `(import [m [*]])` / `(export [m [*]])` glob shape versus the `(import [m [name]])` specific shape is carried by the *form* before the two collapse into shape-identical inner-scope entries), but under this ruling that distinction is **not consulted for the collision decision**: both shapes collide. The check is a pure property of the module's binding set at the point the later-arriving form is processed (the definition when the import already bound the name; symmetrically the import when a local definition already bound it), so it is order-independent and needs no call-history state. This is a consequence of the rule, not an implementation mandate about how to store entries.

**Standard-library consequence (informative — import hygiene, not a type question).** A domain module (including the prelude and stdlib modules) that today glob-imports or glob-re-exports a source module (e.g. `(export [primitives [*]])`) **and** defines a name that source also provides (e.g. its own `Option`/`Some`/`None`) is, under this ruling, authoring the very collision this section rejects. The fix is import hygiene: such a module must **not** import a name it defines — it drops the colliding name from the glob's reach (or replaces the glob with a selective import of only the non-colliding names) and **fully-qualifies its references to the colliding source symbol** (`primitives/…`) at the sites that need the source's version. Whether a given stdlib module *should* define its own same-named type or reuse the source module's is a library-design choice governed by the nominal-typing property (§3.8.4) — the two are distinct types either way — and is out of scope for this specification; the normative point here is only that importing-and-redefining one name is an error, and fully-qualified references are the resolution.

### 8.6.5 Ambiguity and Disambiguation

When two **distinct terminal sources** (per the terminal-source comparison in §8.6.4) register the same bare name in a module's symbol table, the name becomes **ambiguous** (poisoned). Attempting to use an ambiguous bare name MUST produce a compile-time error listing the qualified alternatives.

**Glob imports are peers of specific imports — there is no precedence tier.** A bare name brought in by a `[*]` glob participates in ambiguity exactly as a specifically-named import does: the rule is **terminal-source identity**, not import shape. An implementation MUST NOT treat a glob-brought name as a lower-precedence binding that a specific import silently shadows (the "wildcard loses to explicit" / Java model is NOT adopted). Once terminal-source dedup (§8.6.4) is applied, the residual glob-vs-specific overlaps fall into two cases, both handled by the single terminal-source rule:

- **Same terminal** (the common case — the glob's source and the specific import re-export the same original definition): the two entries dedup benignly, no error.
- **Distinct terminals** (genuinely different definitions that happen to share a bare name): the name is poisoned, as for any other same-name collision. This is deliberate footgun protection — overlapping imports of genuinely-different definitions MUST collide rather than one silently winning.

[Tested+Neg tests/spec_08_modules::glob_and_reexport_of_same_terminal_dedup, tests/spec_08_modules::distinct_terminal_overlap_collides]

**Duplicate field names contest the bare ALIAS, not the canonical accessors.** [Tested+Neg tests/spec_field_accessor::bare_alias_ambiguous_canonical_both_work, tests/spec_field_accessor::cross_module_contested_bare_accessor_rejected_neg, tests/spec_field_accessor::cross_module_contested_canonical_accessors_no_cliff] When two in-scope type definitions own a field with the same name (§5.2.6), it is the single **bare alias** (`v`) that cannot pick a target — using it is a compile-time error listing the canonical alternatives (`Box.v`, `Cup.v`), exactly as any other distinct-terminal bare-name collision. The **canonical accessors `Box.v` and `Cup.v` are not affected**: each is a distinct, always-valid function (§8.5.2 — the dotted form is the canonical accessor name, not a poison-only escape). The field therefore stays reachable in every case via its canonical accessor (`Box.v` / `Cup.v`, same-module and cross-module), via `match` (§6), and cross-module via module-qualification (§8.5.1).

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

Ambiguity disambiguation is the **only** routine reason to reach for the dotted form. In non-ambiguous code, bare names are the canonical access form and dotted access (per §8.5.2) is rarely written — it remains available as a derived consequence of the parent type or trait being in bare scope, but offers no additional reach beyond the bare name.

### 8.6.6 Qualified Name Resolution Order

For a qualified name `module_path/local_name` (per §1.4.3, where `module_path` is one or more dot-separated segments and `local_name` is a single symbol, dotted symbol, or operator symbol), resolution proceeds:

1. If `module_path` matches a module alias (from an aliased import, §8.3.4), resolve in the aliased module.
2. If `module_path` (or one of its dot-separated prefixes) matches a module that declares a public mount alias (from an aliased export, §8.4.4) for the next unmatched segment, follow the alias chain through the mounted source module.
3. If `module_path` matches a child module of the current module, resolve there.
4. If `module_path` is a full module path matching a known module, resolve directly.
5. Otherwise, it is a compile-time error: unknown module.

**Alias substitution operates on dot-separated segments of `module_path` (per §1.4.3), NOT across `/`.** The resolver walks `module_path` segment-by-segment, looking for the longest dot-separated prefix that resolves to a known module. At that hit, it checks the resolved module's alias table for the next segment; on hit, the alias's target replaces the matched segment, and resolution restarts on the rewritten `module_path`. This continues until either a full `module_path` match resolves, the chain-follow depth limit is reached, or no further substitution is possible (unknown module). The single `/` in the qualified name is reached only AFTER `module_path` resolves to a known module; the `/` is never crossed during alias substitution.

The target symbol MUST be public in the resolved module. Accessing a private name through a qualified reference is a compile-time error.

### 8.6.7 Impl Resolution Boundary [S66]

When resolving a trait method call (per [§7.4](07-traits.md#74-method-resolution-static-dispatch)), the implementation MUST consider only impls reachable through the **transitive import closure of the current module**. Impls in modules that the current module does not transitively import — even modules that happen to be loaded into the same compilation unit — MUST NOT participate in resolution.

This is the operational consequence of the visibility rule in [§5.11.1](05-definitions.md#5111-impl-visibility--transitive-import-closure): two unrelated modules in a project, each defining its own impl for the same `(Trait, Type)` pair, do not collide so long as no third module transitively imports both. The impl search space is bounded by the import graph, not by global module-table iteration.

The lookup mechanism — whether the typechecker pre-computes a per-module impl index at module-load time, or walks `current_module.imports` on demand at each call site — is **implementation-defined**. The spec pins the visibility rule (which impls a call site CAN see), not the algorithm.

## 8.7 Visibility [Tested tests/spec_08_modules::private_defn_not_importable_neg]

### 8.7.1 Public by Default

All definitions are public by default. Public names are accessible from other modules via `import` or qualified reference.

> **Trait implementations** have no public/private split — `impl` has no `-` variant. See [§5.11.1](05-definitions.md#5111-impl-visibility--transitive-import-closure) and [§8.4.8](#848-implicit-impl-re-export) for the impl-specific visibility rule (transitive import closure of the trait + type).

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

### 8.7.3 Private Name Semantics [Tested+Neg tests/spec_08_modules::glob_import_excludes_private_neg]

A private name:

- Is accessible within the defining module.
- Is accessible within the submodule subtree of the defining module.
- MUST NOT be exported, even with `[*]` glob exports. Glob exports include only public names.
- MUST NOT be accessed via qualified reference from outside the defining module's subtree. A qualified reference to a private name from an external module is a compile-time error.

**Example:**

```clojure
;; main/util.cl  -> module "main.util" (nested child of main.cl, per §8.2.5)
(defn helper [:Int x] :Int (+ x 1))         ; public
(defn- internal [:Int x] :Int (* x x))       ; private

;; main.cl
(mod util)                      ; resolves to main/util.cl (module main.util)
(import [main.util [helper]])   ; ok
(import [main.util [internal]]) ; error: 'internal' is not public in 'main.util'

(main.util/helper 42)           ; ok
(main.util/internal 42)         ; error: 'internal' is private
```

## 8.8 Prelude [Tested tests/spec_08_modules::def1_prelude_provided_defn_called_bare_enters_codegen_batch, tests/spec_08_modules::prelude_like_reexport_compiles]

### 8.8.1 Implicit Import

When a module's source does not reference `prelude` in any `import` or `export` form, the implementation MUST make the prelude's public names available to that module as bare symbols, with the same effect as if the module had written:

```clojure
(import [prelude [*]])    ; implicit -- injected by the compiler
```

The prelude is supplied as an **outer scope** (per §8.6.4): the prelude's public bindings are NOT copied into the module's symbol table; instead, the implementation **activates a prelude-resolution fallback** for the module, so that a bare name that misses in the module's own (inner) scope is resolved against the `prelude` module's public bindings. This is the scope-layering view of "injecting the implicit prelude" — the fallback is on, not a set of materialised bindings. The observable effect is identical to a glob import of the prelude's public names, except that explicit imports and local definitions shadow prelude names structurally (inner scope consulted first) and never collide with the prelude (§8.6.4).

An explicit `(import [prelude [...]])` or `(export [prelude [...]])` suppresses the implicit prelude — i.e. the prelude-resolution fallback is NOT activated for that module. The module author may import specific prelude names (those named bindings enter the inner scope as ordinary explicit imports, with no fallback), suppress the prelude entirely with a null import (§8.3.6), or re-export prelude symbols without receiving the implicit fallback. In every case the rule is the same: a module that references `prelude` gets no implicit fallback; a module that does not gets the fallback activated.

A `(mod prelude)` declaration does not suppress the implicit fallback, but the declared submodule shadows the library prelude during module resolution.

### 8.8.2 Regular Module Semantics

The prelude uses normal module resolution (Section 8.11.2) with no special search paths. It is discovered, loaded, and compiled as a regular module through the standard compilation pipeline -- it participates in the module graph like any other module and is compiled in topological order (its dependencies first, then the prelude, then user modules).

A project MAY provide its own `prelude.cl` that shadows a library prelude, since module resolution checks the project directory before the stdlib directory.

### 8.8.3 Empty Prelude

An empty prelude is valid. The core language -- primitives, special forms, type inference -- works without any prelude content. The prelude provides convenience (traits, operators, types, macros) but is not required for the language to function.

```clojure
;; A valid, empty prelude.cl
```

## 8.9 Synthetic Modules [Tested tests/spec_08_modules::synthetic_primitives_module_available]

Synthetic modules are registered by the runtime without corresponding `.cl` source files. They provide compiler-seeded types, built-in functions, and platform bindings.

### 8.9.1 The `primitives` Module

The `primitives` module contains:

- **Builtin types**: `Int`, `Bool`, `String`, `Float`, `Vec`
- **The IO ADT**: `(deftype (IO a) (IOVal [:a ioval]))` -- the compiler-seeded IO type
- **Primitive functions**: The specific catalog of primitive functions is implementation-defined. See [Appendix A](appendix-a-builtins.md) for the reference implementation's catalog.

All names in `primitives` -- both primitive types (`Int`, `Bool`, `Float`, `String`) and primitive functions (`add-i64`, `vec-len`, `vec-get`, etc.) -- are stored in qualified form only. They are NOT available as bare names unless brought into scope through:

1. The implicit prelude import (§8.8.1), provided the prelude re-exports the name, OR
2. An explicit import: `(import [primitives [Int]])` or `(import [primitives [add-i64]])`.

Fully-qualified references (`primitives/Int`, `primitives/add-i64`) work regardless of imports.

The §8.11.4 "primitives remain available" guarantee refers to fully-qualified-reference reachability -- not bare-name scope. Without a prelude (or with a prelude that does not re-export the needed names), bare-name use is a compile-time "unknown type" or "unknown name" error; the fully-qualified form continues to work.

[S70]

### 8.9.2 The `macros` Module

The `macros` module contains the `Sexp` and `SList` algebraic data types used by the macro system:

- `Sexp` -- the S-expression ADT with constructors for integers, strings, symbols, lists, and brackets
- `SList` -- a cons-list type with `SCons` and `SNil` constructors

The `macros` module is NOT implicitly imported. The macro expander and `quote-sexp` primitive emit qualified references (`macros/SexpSym`, `macros/SCons`, etc.), so quasiquote-based macros work without importing the module. Modules that directly reference Sexp constructors (e.g., for pattern matching on macro arguments) MUST import or use qualified references eg. `(import [macros [*]])`.

### 8.9.3 Platform Modules [Tested+Neg src/platform.rs::platform_fn_non_io_return_is_rejected]

Platform modules are loaded from dynamic libraries (DLLs) via the `platform` special form:

```clojure
(platform stdio)     ; loads platform.stdio from a DLL
```

The platform name is resolved to a DLL file via the platform DLL search order (§8.11.3). This registers a synthetic module named `platform.stdio` containing the functions exported by the platform library. Every platform function MUST return `IO _`.

A platform function is foreign native code: the compiler cannot inspect its body and therefore cannot verify whether it performs side effects. The compiler MUST trust the declared signature. A platform function whose declared type were pure (e.g. `(Fn [a] b)`) would be treated as pure by the typechecker — eligible for memoization, reordering, elision, and lenient/parallel sparking — while the foreign host is free to perform arbitrary effects. Treating unverifiable foreign code as pure is therefore unsound. The only sound treatment is to require every platform function to sequence its effects through `IO`, so the requirement is **unconditional** — not conditioned on whether the function "appears to" perform side effects. The platform ABI contract (§[10.10](10-io.md#1010-platform-abi-contract)) describes the corresponding C-ABI level. (A trusted-pure foreign-function escape hatch, if ever introduced, would be a separate explicit feature — never the default.)

Platform module names follow the pattern `platform.<name>`.

### 8.9.4 Availability

Synthetic modules are always known to the module system. Their names are seeded into the module name registry so that `(import [primitives [*]])` resolves without file discovery.

## 8.10 Module Compilation Order [Tested tests/spec_08_modules::module_cycle_detection_neg]

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

### 8.11.1 Project Root [Tested tests/spec_08_modules::project_root_shadows_stdlib]

The **project root** is the directory containing the entry file (the `.cl` file passed to the compiler or the REPL's working directory). It anchors all relative path resolution for both modules and platform DLLs.

### 8.11.2 Module Resolution Search Order [Tested tests/spec_08_modules::project_root_shadows_stdlib, tests/spec_08_modules::stdlib_module_compiles_and_runs]

When resolving a module name to a file, the implementation MUST search in this order:

1. **Submodule of current module** -- already registered via `(mod name)` in the current module. No file search is required because the submodule was loaded when the `mod` declaration was processed.
2. **Project root** -- `{project_root}/{name}.cl`. The directory containing the entry file.
3. **Lib directories** -- `{lib_dir}/{name}.cl` for each lib directory, in order.

A module in the project root shadows a module with the same name in a lib directory. This is intentional -- it allows projects to override library modules.

#### 8.11.2.1 Bare-Name Precedence: Current-Module-Relative Submodule Wins [Tested tests/spec_08_modules::project_root_shadows_stdlib]

The search order above is **first-match**: the first tier that yields a file resolves the name, and later tiers are not consulted. This is normative in the one shape where two tiers can both match a bare name — the **dual-name shape**:

> When a bare module name `name` is resolved from **inside** module `M`, and **both** a current-module-relative submodule `M.name` (tier 1, registered via `(mod name)` in `M`) **and** a root module `name` (tier 2, `{project_root}/name.cl`) exist, the resolution MUST bind the **submodule** `M.name`. The current-module-relative submodule wins; the root module is not consulted for that bare reference.

This is the nearest-scope reading: a bare name inside a module first means "the submodule I declared," and only falls through to the project root and lib directories when no such submodule exists. It holds uniformly for every position that resolves a bare module name — `(import [name …])`, `(export [name …])`, and the `(mod name)`-registered reference itself — so a bare name never resolves to the submodule in one position and the root module in another within the same module `M`. To refer to the root module `name` from inside `M` when a submodule `M.name` also exists, name it by its own path (the root module `name` is reachable as the peer it is), not as a bare reference that tier 1 would capture first.

**Example.** Given a project with a root module `child.cl` **and** a submodule `parent.child` (declared by `(mod child)` inside `parent.cl`):

```
project/
  parent.cl           ; contains (mod child)  → loads parent/child.cl as parent.child
  parent/
    child.cl          ; module "parent.child"
  child.cl            ; root module "child" (a peer)
```

Inside `parent`, `(import [child [f]])` resolves `child` to the submodule `parent.child` (tier 1), **not** the root module `child` (tier 2). Both resolution stages of a conforming implementation MUST agree on this: whichever code path binds the name early and whichever collects it late resolve the same bare `child` to `parent.child`. (Implementation follow-up, if the two stages disagree, is `/int`-internal — the semantics pinned here is the contract they must both meet.)

The standard library is not a special language feature beyond this search mechanism. Modules named `core`, `prelude`, `std`, or anything else are ordinary Cranelisp source files found through the module search order — there is no distinction at the language level between "standard library" modules and user modules.

### 8.11.3 Platform DLL Resolution Search Order [Tested tests/wave3_g8.rs]

When resolving a platform name to a DLL (§8.9.3), the implementation MUST search in this order:

1. **Project root** -- `{project_root}/platforms/{name}.{ext}`
2. **Lib directories** -- `{lib_dir}/platforms/{name}.{ext}` for each lib directory, in order.
3. **Platform directories** -- additional directories from platform-specific configuration (§8.11.5).

The file extension `.{ext}` is platform-dependent (`.dylib` on macOS, `.so` on Linux, `.dll` on Windows). The implementation SHOULD also accept the Cargo library naming convention (`libcranelisp_{name}.{ext}`) as an alternative filename at each search location.

Platform resolution mirrors module resolution: project root is checked first, then lib directories in order. This means a project can ship platform DLLs alongside its source (`myproject/platforms/custom-io.dylib`), and a standard library can ship platforms alongside its modules (`stdlib/platforms/stdio.dylib`).

### 8.11.4 Lib Directory Configuration [Tested tests/spec_platforms::cranelisp_toml_lib_dirs_resolves_module]

**The resolved lib-directory set is the additive UNION of all sources (FIXME 0410, settled S91).** [Tested+Neg tests/spec_platforms::cranelisp_lib_env_searched_before_toml_lib_dirs, tests/project_config::lib_dir_union_neg_empty_toml_does_not_suppress] No source ever *replaces* or *suppresses* another: each source only ever **contributes** directories to the set. A `Cranelisp.toml` `lib-dirs` value therefore only ever **adds** paths — it cannot suppress `CRANELISP_LIB`, the programmatic additions, or the `{project_root}/stdlib/` default. (This dissolves the prior "a present/empty config file suppresses the stdlib fallback" footgun entirely: there is no replacing tier, so a default or empty-`lib-dirs` scaffold is always safe.)

The set is assembled from these sources, all of which contribute (union):

1. **Explicit programmatic additions** -- the implementation MUST support adding lib directories in code (e.g., via a session API), including any directory passed via a CLI lib-dir flag.
2. **`CRANELISP_LIB` environment variable**, if set -- a colon-separated list of directory paths. Each entry contributes to the set.
3. **Project configuration file** (`Cranelisp.toml` in the project root) MAY specify a lib directory list under the TOML key `lib-dirs` (a list of path strings); each entry contributes to the set. Paths are resolved relative to the directory containing `Cranelisp.toml`. A malformed `Cranelisp.toml` MUST produce a diagnostic identifying the file path and the parse error. An absent `lib-dirs` key, an absent `Cranelisp.toml`, and `lib-dirs = []` are equivalent here: each contributes nothing — none of them removes any directory contributed by another source.
4. **Default**: `{project_root}/stdlib/`, if that directory exists. It contributes to the set like any other source; it is not a fallback that other sources turn off.

**Search order.** [Tested tests/project_config::lib_dir_search_order_cli_env_toml_stdlib, tests/spec_platforms::cranelisp_lib_env_searched_before_toml_lib_dirs] When a module name resolves to a file present in more than one lib directory, the implementation MUST search the contributing directories in this order and take the **first match** (standard CLI-tool precedence — command-line over environment over config file over built-in default, matching Cargo, where environment variables take precedence over TOML config):

1. CLI lib-dir flag / programmatic additions (source 1),
2. `CRANELISP_LIB` entries (source 2), in their colon-separated order,
3. `Cranelisp.toml` `lib-dirs` entries (source 3), in their listed order,
4. `{project_root}/stdlib/` default (source 4) — searched **last**.

(Note this places `CRANELISP_LIB` **before** `Cranelisp.toml` in search order — env over config file, per the cited CLI-tool convention.)

If no source yields any lib directory, the lib directory list is empty. No lib modules (including `prelude` and `core`) will be found. The language still functions — primitives and special forms remain available — but no standard library names are in scope.

"Primitives remain available" means **fully-qualified** reachability (e.g., `primitives/Int`, `primitives/add-i64`). Bare-name references to primitive names require prelude re-export or explicit import; see [§3.1](03-types.md#31-primitive-types) and [§8.9.1](#891-the-primitives-module).

Special forms (`defn`, `let`, `if`, `match`, etc.) are not module names and have no import requirement; they are always available as bare references regardless of prelude or imports.

[S70]

> **Practical implication.** The project root is the directory containing the entry file. A project at `exemplar/solver.cl` has project root `exemplar/`. If `exemplar/stdlib/` does not exist and `CRANELISP_LIB` is not set, the prelude will not load. To use the standard library from a subdirectory project, either:
> - Set `CRANELISP_LIB` to point to the stdlib location (e.g., `CRANELISP_LIB=../stdlib`), or
> - Create a project configuration file that specifies the lib path, or
> - Symlink or copy `stdlib/` into the project root.

### 8.11.5 Platform Directory Configuration

Additional platform-specific search directories are assembled as the **additive UNION** of the following sources — mirroring §8.11.4 (FIXME 0410). The same union semantics, search order, and diagnostic requirements apply, with `platform-dirs` in place of `lib-dirs` and `CRANELISP_PLATFORM_PATH` in place of `CRANELISP_LIB`. No source replaces or suppresses another; each only contributes.

1. **Explicit programmatic additions** -- the implementation MUST support adding platform directories in code (e.g., via a session API), including any directory passed via a CLI flag.
2. **`CRANELISP_PLATFORM_PATH` environment variable**, if set. A colon-separated list of directory paths; each entry contributes.
3. **Project configuration file** (`Cranelisp.toml` in the project root) MAY specify a platform directory list under the TOML key `platform-dirs` (a list of path strings); each entry contributes. Paths are resolved relative to the directory containing `Cranelisp.toml`. A malformed `Cranelisp.toml` MUST produce a diagnostic identifying the file path and the parse error (same requirement as §8.11.4). An absent `platform-dirs` key, an absent `Cranelisp.toml`, and `platform-dirs = []` are equivalent: each contributes nothing and removes nothing.

Search order on a name present in more than one directory is first-match, in the order above (CLI/programmatic → `CRANELISP_PLATFORM_PATH` → `Cranelisp.toml` `platform-dirs`) — env over config file, per §8.11.4.

There is no default fallback tier: unlike lib directories (§8.11.4, tier 4), platform DLLs bundled with the standard library are already reached via §8.11.3 tier 2 (`{lib_dir}/platforms/`). If none of the sources above yield any entries, the additional platform directory list is empty and only project-root and lib-directory `platforms/` subdirectories are searched.

These directories are searched after project root and lib directories (§8.11.3, tier 3). They are intended for platform DLLs that are not co-located with source modules — for example, system-wide installations or Cargo build output during development.

> **Development convenience.** During development, set `CRANELISP_PLATFORM_PATH=target/debug` so that `cargo build` output is found automatically without copying DLLs into `platforms/`.

### 8.11.6 Standard Library Structure (Reference Implementation)

There is no language-level requirement for the standard library structure.

## 8.12 Macro Interaction [Tested crates/cranelisp-frontend/src/module_extract.rs::test_passthrough]

### 8.12.1 Pre-Expansion Processing

The `mod`, `import`, and `export` forms MUST be extracted from raw S-expressions before macro expansion. They are NOT subject to macro expansion.

### 8.12.2 Cross-Module Macro Availability

Macros from imported modules are available for expansion in the importing module. Since modules compile in topological order, a macro's compiled expansion function is available by the time any importer needs it.

### 8.12.3 Macro Hygiene

Macro authors SHOULD use qualified names for non-prelude references within macro bodies to avoid capture by the importing module's local names.

## 8.13 REPL Integration [Tested crates/cranelisp-typecheck/src/checker/tests.rs::test_default_module_is_user]

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
| `(import [(mod alias) [names]])` | Import names + register private module alias | N/A |
| `(import [mod [(src local) ...]])` | Renamed import — bind source name as local | N/A |
| `(import [super [*]])` | Import from parent module | N/A |
| `(export [mod [names]])` | Re-export names as public API | Public |
| `(export [(mod alias) [names]])` | Re-export names + mount module at public alias | Public |
| `(export [mod [(src local) ...]])` | Renamed re-export — exported name differs from source | Public |
| `module/name` | Qualified name reference | N/A |
| `Type.member` | Dotted member access | N/A |
| Leading `;;` comment block (file head) | Module preamble — module-level documentation (§8.16) | Metadata (public-readable) |

## 8.15 Complete Example [S10]

The following example demonstrates the full module system in a project with multiple files, imports, exports, visibility, and qualified access.

Per §8.2.5, every `(mod name)` resolves to the nested child path `{stem}/{name}.cl`. So `main.cl`'s `(mod shapes)` loads `main/shapes.cl` (module `main.shapes`), and that file's `(mod display)` in turn loads `main/shapes/display.cl` (module `main.shapes.display`). Submodules are always nested under their declaring file's directory — never siblings:

```
project/
  main.cl                   ; root module (entry point)
  main/
    shapes.cl               ; module "main.shapes"
    shapes/
      display.cl            ; module "main.shapes.display"
```

```clojure
;; main/shapes.cl  -> module "main.shapes"
(mod display)               ; resolves to main/shapes/display.cl

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
;; main/shapes/display.cl  -> module "main.shapes.display"
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
(mod shapes)               ; resolves to main/shapes.cl (module main.shapes)
(platform stdio)
(import [main.shapes     [circle rect Shape Circle Rect]
         platform.stdio  [*]])

(defn main []
  (do
    (print (show (circle 2.5)))              ; uses imported 'circle' and 'show'
    (print (show (rect 3.0 4.0)))            ; uses imported 'rect'
    (print (show (main.shapes/circle 1.0)))  ; qualified access also works
    ))
```

## 8.16 Module Preamble [S88]

A **module preamble** is module-level documentation: the module analogue of a definition docstring (§5.12). Where a `defn` docstring documents a function, a module preamble documents the module as a whole — its purpose, its public surface's intent, design notes. It is the module-level realization of the self-documenting principle (root `CLAUDE.md` §"Design Principles") and is purely additive: a module **without** a preamble is valid, exactly as the optional-prelude principle requires (§8.8.3).

### 8.16.1 Syntax and Position [S88]

The module preamble is the **contiguous leading line-comment block** at the top of the file — file-header documentation, the natural place a module's purpose is written. It is the module-level analogue of a `defn` docstring (§5.12), but realized through comments rather than a string literal (§8.16.6 explains the deliberate asymmetry). It requires no new keyword and no new reader construct: a `;;` comment block is already valid syntax (§1.2); the preamble role is purely positional.

```ebnf
module_preamble = comment_line+    (* a contiguous leading line-comment block; see §1.2 *)
```

**Boundary rule.** The preamble is the **contiguous block of line comments that begins on the first line of the file and runs up to (but not including) the first form** — whether that first form is a structural form (`mod`, `import`, `export`, `platform`) or a module-body form (a `defn`, trait-impl, expression, etc.). The natural file-header position is **above `(mod …)`**. Concretely:

- The block **starts at the first line of the file**. Comments that begin further down — after any form has already appeared — are never preamble.
- The block is **terminated by the first non-comment form**. The block extends through every contiguous comment line up to that first form.
- A **blank line breaks the block.** Only the contiguous run of comment lines starting at the file's first line forms the preamble; if a blank line interrupts the leading comments before the first form, the preamble is the run **above** the first blank line, and the comment lines below the blank line are ordinary comments. (This lets an author write a short file-header preamble, then a blank line, then ordinary section comments, without the latter being absorbed into the documentation.)
- Comments appearing **after the first form** are ordinary comments, never preamble — regardless of content.
- **At most one** preamble exists per module: the single contiguous leading block defined above. There is no second preamble.

```clojure
;; Sudoku solver: constraint propagation +
;; backtracking over a Vec-backed grid.
(mod solver)                                  ; first form terminates the preamble block
(import [collections.vec [conj]])

(deftype Grid [:Vec cells])
(defn solve [:Grid g] :Grid ...)
```

The contiguous `;;` block at the file's head — `"Sudoku solver: constraint propagation + backtracking over a Vec-backed grid."` — is the module preamble. It sits **above** `(mod solver)`, the file-header position.

A module with no leading comment block has **no preamble** (the common, valid case):

```clojure
(defn helper [:Int x] :Int (+ x 1))   ; util.cl -> module "util" — no preamble, valid
```

### 8.16.2 Stored Representation [S88]

The stored preamble **text** is the comment block's content with comment markers stripped and lines joined:

- Each comment line contributes its content with the leading `;;` (or `;`) marker **and one immediately-following space, if present,** stripped. (`;; Sudoku solver` contributes `Sudoku solver`; a bare `;;` line contributes the empty string.)
- The stripped lines are **joined with a newline (`\n`)**, preserving the block's internal line structure. A two-line comment block becomes a two-line string with one interior newline.
- This joined text is the value stored on the per-module symbol table as `SymbolTable.module_preamble: Option<String>` (FIXME 0428 — the field shape is `Option<String>`, **unchanged**; only the *source* of the text is the leading comment block rather than a string literal).
- A module with **no** leading comment block stores `None` — a valid, common state, consistent with the optional-prelude principle (§8.8.3). The absence of a preamble is never an error.

### 8.16.3 Semantics [S88]

- The preamble has **no effect on program semantics**. Like a docstring (§5.12) — and like any comment — it is metadata only: not evaluated, producing no value, entering no module's value namespace.
- The preamble is stored in the module's compilation metadata (§8.16.2), parallel to per-definition docstrings (§5.12), and is available for introspection (§8.16.4).
- Recognizing the preamble requires the **reader to surface the leading comment block** rather than discard it, and associate it with the module. Comments are ordinarily discarded; the leading comment block is **semantically captured, not discarded**. (The implementation is a frontend-reader concern — `/design (cranelisp-frontend)`'s — not the spec's; the spec pins only that the leading comment block is captured and stored, leaning on the `Sexp::Comment` preservation added in Sprint 24, §1.2.)

### 8.16.4 Reading the Preamble [S88]

The preamble is the module-level entry on the same introspection surface as docstrings. A conforming REPL's module-documentation command (the `/doc <module>` family) MUST be able to return a module's preamble text, and MUST indicate when a module has no preamble (the documentation-read analogue of a definition with no docstring, §5.12).

> **NOTE — experience is `/repl`-owned.** This subsection pins only the spec-level *read result*: `/doc <module>` returns the module's preamble text (or a no-preamble indication). The command's exact output formatting, framing, aliases, and interaction with `/doc <name>` (the definition-docstring read, `repl/spec.md` §3.1) are the REPL experience contract, authored by `/repl` in `repl/spec.md`. This section does not constrain that presentation beyond the read-result requirement above.

### 8.16.5 Edit Path and Source-Regeneration Stability [S88]

A module preamble is **editable in-session** (the basis for the agent's Document-mode preamble maintenance, `design/arch/repl-embedded-agent.md` §3.1/§3.4): a REPL or tool MAY set or replace a module's preamble, which rewrites the leading comment block in the module's backing file.

When a module's source is regenerated — the same source-regeneration path that rewrites a parent file on inline-submodule extraction (§8.2.2) and writes `(mod …)` backing files (§8.2.5) — the preamble MUST **round-trip byte-stably**:

- A module whose preamble is **unchanged** across a regeneration MUST have a byte-identical leading comment block before and after. The regenerator MUST NOT reflow, re-wrap, re-indent, or re-mark an unmodified preamble comment block.
- The preamble MUST be re-emitted in its canonical leading position (§8.16.1) — the contiguous comment block at the head of the file, above the first form — so that a regenerated file re-parses to the same preamble.
- Setting a preamble on a module that has none inserts the leading comment block at the head of the file; clearing a preamble removes that block and MUST leave the rest of the file byte-stable.

This byte-stability requirement **coordinates with the live FIXME 0423 fix.** The round-trip leans on `Sexp::Comment` preservation (added Sprint 24, §1.2): the **frontend reader captures the leading comment block** (rather than discarding it, §8.16.3), and the **regen pretty-printer must re-emit it verbatim** — the same source-regen path FIXME 0423 is correcting (CWD-relative write + annotation spacing) for `(mod …)` backing-file regeneration (§8.2.5). The preamble comment block participates in that round-trip on equal footing with the rest of the file: an extraction or regen that touches a module carrying a preamble MUST preserve the preamble comment block verbatim unless the preamble itself is the thing being edited. The preamble round-trip and the 0423 fix therefore share, and must be reconciled on, the one regen pretty-printer path.

### 8.16.6 Why a Comment Block, Not a String Literal [S88]

The preamble is a **comment block**, whereas a `defn` docstring (§5.12) is a leading **string literal**. This asymmetry is deliberate:

- A `defn` (or `deftype`, `deftrait`, …) has a **binding form** that can unambiguously carry a leading string literal in a fixed position — between the name and the parameter list. The string literal's docstring role is anchored by that surrounding form.
- A **module has no enclosing binding form**: a file is a flat sequence of top-level forms. A leading bare string literal in module-body position would be ambiguous and fragile (is it documentation, or a top-level expression whose value is discarded?), and would interact awkwardly with the pre-expansion structural forms (`mod`/`import`/`export`/`platform`) that are extracted before the module body.
- **File-header comments are where module documentation naturally lives** — every author already writes the module's purpose as a `;;` block at the top of the file. Promoting that existing convention to the preamble role requires no relocation of where documentation is written and no new syntax.

So the two documentation surfaces use different lexis by design: string-literal docstrings for *named definitions* (anchored by a binding form), and a leading comment block for the *module as a whole* (anchored by file-header position).

### 8.16.7 Summary Row [S88]

Added to the §8.14 form summary:

| Form | Purpose | Visibility |
|---|---|---|
| Leading `;;` comment block (file head) | Module preamble — module-level documentation | Metadata (public-readable) |
