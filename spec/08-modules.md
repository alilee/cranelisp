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

### 8.2.3 Private Submodule Declaration [Tested+Neg tests/ring2.rs::neg_private_submodule_not_importable_from_peer]

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

### 8.3.1 Specific Name Import [Tested+Neg tests/ring2::import_specific_names, tests/sprint59_neg::import_of_non_existent_name_errors_neg]

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

### 8.3.8 Super Import [Tested+Neg tests/modules::super_import_at_root_is_rejected_neg, tests/sprint59_neg::super_import_at_repl_prompt_rejected_neg]

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

### 8.3.10 Placement [Tested+Neg tests/sprint59_neg::import_below_use_still_available_before_definitions, tests/sprint59_neg::import_inside_let_rejected_neg]

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

### 8.4.8 Implicit Impl Re-export [R4 S66]

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

Qualified-name resolution per §8.6.6 walks module alias chains. Alias substitution operates on the dot-separated segments of `module_path` (within the grammar above), NOT across `/`. If the current resolution scope contains a public mount alias under module `current-module` that maps the segment `str` to `core.string` (per §8.4.4), then writing `current-module.str/split` causes the resolver to walk `module_path` segment-by-segment: it finds `current-module`, looks up `str` in that module's alias table, substitutes `core.string`, and then resolves `split` in `core.string`. Mount aliases declared by `export` are public; alias-imports declared by `import` (§8.3.4) are private to the importing module.

### 8.5.2 Dotted Names

The `.` within a name provides access to members of types and traits:

```clojure
Option.Some             ; constructor 'Some' of type 'Option'
Option.None             ; constructor 'None' of type 'Option'
Display.show            ; method 'show' of trait 'Display'
Num.+                   ; operator '+' of trait 'Num'
```

Dotted names resolve directly from the parent type or trait definition, bypassing the bare-name lookup. This means they work even when the bare name is ambiguous (see Section 8.6.5).

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

## 8.6 Name Resolution [Tested tests/ring2.rs::name_resolution_local_shadows_module, tests/ring2.rs::module_qualified_name_resolution]

Name resolution converts source-level names into their definitions. An implementation MUST follow the resolution layers defined in this section.

### 8.6.1 Resolution Layers

Resolution proceeds through three layers, in order:

1. **Local environment**: `let` bindings, `fn` parameters, and `match` pattern variables. These are lexically scoped -- pushed on entry to a binding form and popped on exit.

2. **Module scope**: Definitions within the current module, plus names brought in via `import`. This layer consults the current module's symbol table (the **inner scope**), following `Import` and `Reexport` references to their source modules. When the inner scope misses and the module receives the implicit prelude (§8.8.1), this layer falls back to the prelude's public bindings (the **outer scope**, per §8.6.4) before proceeding to the root module.

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

- **Rename collisions**: Two import (or export) entries — whether via rename or bare — producing the same local (or exported) name MUST produce a compile-time error. Example: `(import [m [(Some X) (None X)]])` is an error — duplicate local name `X`.

- **Mount collisions**: Two export forms mounting different source modules at the same alias path MUST produce a compile-time error. Example: `(export [(core.string foo) [...]] [(core.option foo) [...]])` is an error — duplicate mount alias `foo`.

- **Mount-vs-submodule collisions**: An export mount whose alias collides with an actual submodule `(mod inner)` of the current module MUST produce a compile-time error. Example: if module `A` declares `(mod inner)` AND `(export [(other.mod inner) [...]])`, that's an error — `A/inner` would be ambiguous.

Same-source duplicates (the same name arriving through two re-export paths from the same original definition) are NOT ambiguous.

#### Explicit Imports Shadow the Implicit Prelude [R4 S20]

The implicit prelude is an **outer scope**, not a set of bindings materialised into the module's symbol table. A module's own symbol table is its **inner scope**: it holds only the module's local definitions and its *explicit* imports/re-exports. The implicit prelude (injected per §8.8) is a separate **outer scope** — the `prelude` module's own public bindings — consulted **only on a resolution miss in the inner scope**. Prelude bindings are NOT copied into the module's table.

Because resolution consults the inner scope before falling back to the outer prelude scope, explicit imports and local definitions shadow prelude-provided names automatically — without producing a duplicate-import error. The shadow is a lookup ordering (inner before outer), not a same-table override. This is exactly the scope layering the resolution layers in §8.6.1 describe: explicit imports take precedence over the implicit prelude, just as inner `let` bindings shadow outer ones.

The conflict rules above (duplicate imports, definition-over-import, rename/mount collisions, and the §8.6.5 ambiguity poisoning) operate over the **inner scope only** — the module's local definitions and its explicit imports. The implicit-prelude outer scope never participates in these checks: a name an explicit import (or a local definition) provides does not collide with a same-named prelude binding, because the prelude binding is not in the inner table. Two *explicit* entries that produce the same local name remain a conflict exactly as before.

When an explicit glob import brings in a name that the prelude would also provide, the explicit version (in the inner scope) is found first, and the prelude's binding is simply never consulted for that bare name. This means the module loses bare-name access to the prelude's binding. Remediation strategies:

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

### 8.6.7 Impl Resolution Boundary [R4 S66]

When resolving a trait method call (per [§7.4](07-traits.md#74-method-resolution-static-dispatch)), the implementation MUST consider only impls reachable through the **transitive import closure of the current module**. Impls in modules that the current module does not transitively import — even modules that happen to be loaded into the same compilation unit — MUST NOT participate in resolution.

This is the operational consequence of the visibility rule in [§5.11.1](05-definitions.md#5111-impl-visibility--transitive-import-closure): two unrelated modules in a project, each defining its own impl for the same `(Trait, Type)` pair, do not collide so long as no third module transitively imports both. The impl search space is bounded by the import graph, not by global module-table iteration.

The lookup mechanism — whether the typechecker pre-computes a per-module impl index at module-load time, or walks `current_module.imports` on demand at each call site — is **implementation-defined**. The spec pins the visibility rule (which impls a call site CAN see), not the algorithm.

## 8.7 Visibility [Tested tests/ring2.rs::visibility_private_defn_not_importable, tests/ring2.rs::visibility_public_defn_importable, tests/ring2.rs::visibility_private_deftype_not_importable]

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

## 8.9 Synthetic Modules [Tested tests/ring2.rs::synthetic_primitives_module_available]

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

[R4 S70]

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

### 8.11.4 Lib Directory Configuration [Tested tests/e2e.rs::e2e_cranelisp_lib_env_overrides_stdlib, tests/e2e.rs::e2e_cranelisp_toml_lib_dirs_resolves_modules, tests/e2e.rs::e2e_cranelisp_toml_overrides_cranelisp_lib_env, tests/e2e.rs::e2e_cranelisp_toml_missing_falls_through_to_env, tests/e2e.rs::e2e_cranelisp_toml_malformed_errors_helpfully]

Lib directory locations are assembled from the following sources, in precedence order:

1. **Explicit programmatic additions** -- the implementation MUST support adding lib directories in code (e.g., via a session API). These take highest precedence and are appended to the list.
2. **Project configuration file** (`Cranelisp.toml` in the project root) MAY specify a lib directory list under the TOML key `lib-dirs` (a list of path strings). When present, this takes precedence over `CRANELISP_LIB` and the default fallback. Paths are resolved relative to the directory containing `Cranelisp.toml`. A malformed `Cranelisp.toml` MUST produce a diagnostic identifying the file path and the parse error.
3. **`CRANELISP_LIB` environment variable**, if set. A colon-separated list of directory paths. When set (even to empty), it fully controls the default lib directory list — no fallback is applied.
4. **Default fallback**: When neither a project configuration file nor `CRANELISP_LIB` is present, the implementation SHOULD use `{project_root}/stdlib/` as the sole default lib directory, if that directory exists.

If no sources yield any lib directories, the lib directory list is empty. No lib modules (including `prelude` and `core`) will be found. The language still functions — primitives and special forms remain available — but no standard library names are in scope.

"Primitives remain available" means **fully-qualified** reachability (e.g., `primitives/Int`, `primitives/add-i64`). Bare-name references to primitive names require prelude re-export or explicit import; see [§3.1](03-types.md#31-primitive-types) and [§8.9.1](#891-the-primitives-module).

Special forms (`defn`, `let`, `if`, `match`, etc.) are not module names and have no import requirement; they are always available as bare references regardless of prelude or imports.

[R4 S70]

> **Practical implication.** The project root is the directory containing the entry file. A project at `exemplar/solver.cl` has project root `exemplar/`. If `exemplar/stdlib/` does not exist and `CRANELISP_LIB` is not set, the prelude will not load. To use the standard library from a subdirectory project, either:
> - Set `CRANELISP_LIB` to point to the stdlib location (e.g., `CRANELISP_LIB=../stdlib`), or
> - Create a project configuration file that specifies the lib path, or
> - Symlink or copy `stdlib/` into the project root.

### 8.11.5 Platform Directory Configuration

Additional platform-specific search directories are assembled from the following sources, in precedence order. This list mirrors §8.11.4; the same precedence and diagnostic requirements apply, with `platform-dirs` in place of `lib-dirs` and `CRANELISP_PLATFORM_PATH` in place of `CRANELISP_LIB`.

1. **Explicit programmatic additions** -- the implementation MUST support adding platform directories in code (e.g., via a session API). These take highest precedence and are appended to the list.
2. **Project configuration file** (`Cranelisp.toml` in the project root) MAY specify a platform directory list under the TOML key `platform-dirs` (a list of path strings). When present, this takes precedence over `CRANELISP_PLATFORM_PATH`. Paths are resolved relative to the directory containing `Cranelisp.toml`. A malformed `Cranelisp.toml` MUST produce a diagnostic identifying the file path and the parse error (same requirement as §8.11.4).
3. **`CRANELISP_PLATFORM_PATH` environment variable**, if set. A colon-separated list of directory paths.

There is no default fallback tier: unlike lib directories (§8.11.4, tier 4), platform DLLs bundled with the standard library are already reached via §8.11.3 tier 2 (`{lib_dir}/platforms/`). If none of the sources above yield any entries, the additional platform directory list is empty and only project-root and lib-directory `platforms/` subdirectories are searched.

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
| `(import [(mod alias) [names]])` | Import names + register private module alias | N/A |
| `(import [mod [(src local) ...]])` | Renamed import — bind source name as local | N/A |
| `(import [super [*]])` | Import from parent module | N/A |
| `(export [mod [names]])` | Re-export names as public API | Public |
| `(export [(mod alias) [names]])` | Re-export names + mount module at public alias | Public |
| `(export [mod [(src local) ...]])` | Renamed re-export — exported name differs from source | Public |
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
