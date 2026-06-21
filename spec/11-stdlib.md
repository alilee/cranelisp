# 11. Standard Library (Non-Normative)

> **This section is non-normative.** It describes the constraints and conventions a standard library for Cranelisp must satisfy. The reference implementation's standard library is documented separately in the user guide.

The Cranelisp language does not mandate a specific standard library. Any conforming implementation MAY provide a different set of library modules, provided it satisfies the language-level guarantees defined in Sections 1–10 and 12. This section describes those guarantees from the perspective of a standard library author.

## 11.1 Language Guarantees to Library Authors [Tested crates/cranelisp-typecheck/src/checker/tests.rs::test_bare_module_has_root_contents_only]

The language guarantees the following regardless of which standard library (if any) is provided:

- **Compiler-seeded synthetic modules**: The `primitives` and `macros` modules are always available. Their contents are normatively specified in [Section 8.9](08-modules.md#89-synthetic-modules) and [Section 9.1](09-macros.md#91-sexp-data-model).

- **Module search order**: The implementation searches for library modules in the locations described in [Section 8.11](08-modules.md#811-lib-directory). A project may shadow any library module by providing a file with the same name in the project root.

- **Implicit prelude injection**: When a module named `prelude` is found on the search path, the compiler injects `(import [prelude [*]])` for all user modules (normatively defined in [Section 8.8](08-modules.md#88-prelude)). An empty prelude is valid — the language does not require the prelude to contain anything.

- **Special forms**: The structural special forms (`defn`, `deftype`, `deftrait`, `impl`, `defmacro`, `let`, `if`, `fn`, `match`, `mod`, `import`, `export`, `platform`) and `trace` are all **root special forms** — parser keywords with distinct syntax, always available without import and with no module path. `trace` produces a distinct trace node; the `Trace` / `TraceCall` types and the field accessors it returns ARE `primitives`-module entries that DO require import — the deliberate form/ADT asymmetry, mirroring `Sexp`-in-`macros` (see [Section 3.2.4](03-types.md#324-trace-type)).

## 11.2 Compiler-Seeded Types [Tested+Neg tests/spec_04_expressions::trace_returns_trace_type, tests/spec_10_io::pure_int_unwraps_inline, tests/trace::trace_adt_names_are_importable_from_primitives, tests/trace::trace_adt_names_not_auto_imported_neg, tests/trace::trace_adt_names_reachable_via_qualified_path_without_import]

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

## 11.3 Bootstrapping Order [Tested tests/spec_11_stdlib::prelude_loads_without_errors, tests/spec_09_macros::defmacro_identity_expands]

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

## 11.4 Writing a Standard Library [Tested tests/spec_11_stdlib::prelude_loads_without_errors]

Practical notes for library authors:

**Sexp types**: Library modules that implement macros using `match` on Sexp variants (e.g., `match arg [(SexpList items) ...]`) MUST include `(import [macros [*]])` or use fully qualified names (`macros/SexpList`). The `macros` module is not auto-imported. Quasiquote-based macros (`\`(if ~cond ~then ~else)`) do not require the import because the expander emits qualified references automatically.

**Primitives**: Library modules that need compiler-seeded functions (arithmetic, string operations, Vec operations) SHOULD import `(import [primitives [*]])`. The `primitives` module is the host for all inline and extern primitives.

**Module compilation order**: Modules compile in topological order (Section 8.10). A macro defined in `core.syntax` is available to `core.collections` if `core.collections` imports `core.syntax`. Library authors must ensure the module dependency graph is acyclic.

**The `~@` operator**: The unquote-splicing operator (`~@expr`) requires `sconcat` to be resolvable as `core.syntax/sconcat`. A standard library that uses `~@` in macro bodies must provide this qualified path, or the generated expansion code will fail to compile. The reference implementation satisfies this by providing `core.syntax` with a public `sconcat` function.

**Prelude design**: The prelude module is the mechanism by which library names become globally available. A standard library SHOULD provide a `prelude.cl` that re-exports the names it considers universally useful. The prelude itself must not import the prelude (it is excluded from implicit prelude injection).

## 11.4a Curated Collection-Verb Naming Reservation (Non-Normative) [S87]

> **This subsection is non-normative guidance to standard-library authors.** It records a forward-compatibility reservation so that the *bare-name surface* a library curates today does not collide with a future trait-dispatched collection abstraction. It changes no language semantics — the reservation operates entirely within the bare-name-curation freedom a library already has under §11.4 and §8.8. The fully-qualified path (`primitives/<name>`, `collections.vec/get`, …) is unaffected and reachable regardless of any reservation (§8.9.1, §8.11.4, §3.1).

A standard library that grows toward a unified, trait-dispatched collection interface (a `Functor`/`Foldable`-style abstraction — see §7.2, §7.7.5, and the §7.12.2 future-extensions table) will eventually want a small set of Clojure-aligned verbs as the *single overload-unified entry point* across `List`/`Vec`/`Seq`. Those verbs are most naturally bound as bare names by the *trait* that owns them, so that one bare call site dispatches to the right concrete family.

To keep an interim curated surface forward-compatible with that future trait, a standard library SHOULD treat the following names as **reserved for future trait-dispatched dispatch** and SHOULD NOT pre-bind them as bare prelude names to a single concrete family in the interim:

| Reserved bare name | Reserved for | Interim guidance |
|---|---|---|
| `map` | future Functor/collection-trait method | Keep concrete families disambiguated (`vec-map`, `map-list`, `seq-map`). Do NOT re-export a bare `map` to one family. |
| `filter` | future collection-trait method | Keep `vec-filter`, `filter-list`, … . Do NOT bare-promote to one family. |
| `reduce` | future Foldable/collection-trait method | Keep `vec-reduce`, `fold-list`, … . Do NOT bare-promote to one family. |
| `count` | future collection-trait method | MAY curate a module-local wrapper (`collections.vec/count`), reachable module-qualified. Do NOT re-export bare `count` through the prelude until the trait owns the name. |
| `get` | future collection-trait method | MAY curate `collections.vec/get`, reachable module-qualified. Do NOT re-export bare `get` through the prelude until the trait owns the name. |
| `conj` | future collection-trait method | MAY curate `collections.vec/conj`, reachable module-qualified. Do NOT re-export bare `conj` through the prelude until the trait owns the name. |
| `assoc` | future collection-trait method | MAY curate `collections.vec/assoc`, reachable module-qualified. Do NOT re-export bare `assoc` through the prelude until the trait owns the name. |

The distinction is **bare-promotion vs. module-qualified curation**:

- **Curating a wrapper inside its family module** (e.g. `collections.vec/count` wrapping `vec-len`) is always permitted, even for a reserved name. The wrapper is reachable module-qualified or via an explicit `(import [collections.vec [count]])`. Binding the name *inside its own module* does not pre-empt the future trait — the trait owns the *bare* name surfaced through the prelude, not the qualified path.
- **Bare-promoting to the prelude** — re-exporting `count`/`get`/`conj`/`assoc` (etc.) as a bare name through the prelude, pointing at one concrete family — is the action that collides with the future trait method of the same name and is what this reservation asks authors to defer.

### 11.4a.1 `first`/`rest` — list vs. pair coexistence

`first`/`rest` are the Clojure idiom for the head/tail of a sequence, and a future sequence trait is the natural owner of the bare names. A standard library MAY rename its concrete list accessors to `first`/`rest` *within the list module* (e.g. `collections.list/first`, `collections.list/rest`), and a `collections/pair` module MAY independently define `first`/`second` as pair accessors. These coexist without conflict **as long as neither bare `first` is re-exported through the prelude**: the two live in distinct modules and are reachable by their fully-qualified paths (`collections.list/first`, `collections.pair/first`).

Re-exporting *both* bare `first` names through one prelude would poison the name under §8.6.4 — the two accessors chain-follow to **distinct terminal sources** (the list `Def` and the pair `Def`), so the bare name is ambiguous (§8.6.5). A standard library SHOULD therefore leave bare `first`/`rest` unbound in the prelude until the future sequence trait decides which abstraction owns them; the concrete accessors stay reachable module-qualified in the interim. (This is the same terminal-source collision rule that governs any two distinct definitions sharing a bare name; the reservation is the author-side discipline that avoids triggering it.)

### 11.4a.2 What the reservation does NOT restrict

The reservation is purely about *which bare names a library promotes to the prelude in the interim*. It does not:

- restrict the fully-qualified path — `collections.vec/get`, `collections.pair/first`, `primitives/<name>` are always reachable (§8.9.1, §8.11.4);
- restrict explicit on-demand import — `(import [collections.vec [count get conj assoc]])` is always available to a user who wants the concrete verbs bare in their own module;
- mandate that the future trait ever be built — it is a forward-compatibility courtesy, not a language requirement;
- affect the trait-dispatched operator surface (`+`, `-`, `*`, `/`, `=`, `<`, `>`, `<=`, `>=`, `show`), which is already trait-dispatched (§7.5) and unaffected — those names are bound by the trait, exactly the model the reserved verbs anticipate.

## 11.5 Trace Support [S20]

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
