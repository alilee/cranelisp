# Modules — files, imports and public names

Split a program into files when you want separate namespaces or reusable code.
A file's path gives its module name; no namespace declaration goes inside it.
This guide uses the default prelude. Its arithmetic examples call primitives
explicitly so their dependencies are visible.

## A two-file program

Create these two files in an empty project directory. `mathx.cl` defines a peer
module; `app.cl` imports one of its public names:

<!-- sample: {"kind":"definition"} -->
```clojure
;; mathx.cl
(defn square [:Int x] (primitives/mul-i64 x x))
(defn- secret [] 99)
(deftype Shade Red Blue)
```

<!-- sample: {"kind":"definition","files":{"mathx.cl":"(defn square [:Int x] (primitives/mul-i64 x x))\n(defn- secret [] 99)\n(deftype Shade Red Blue)\n"}} -->
```clojure
;; app.cl
(import [mathx [square]])
(defn main [] (primitives/Pure (square 7)))
```

Run `cranelisp --run app` from that directory. It prints nothing and exits `49`:
`Pure` returns the square without performing an effect. These are **two files**,
not one source block to paste into the REPL. All examples below use this project
unless another layout is given.

The project root is the base for module paths. `mathx.cl` names `mathx`, and
`a/b.cl` names `a.b`. A qualified symbol has a module before `/` and a name after
it: `mathx/square`. A type or trait member uses a dot after its parent name:
`mathx/Shade.Red`. See [spec §8.1](../../spec/08-modules.md#81-file-to-module-mapping).

A dotted CLI entry uses that same path mapping. In a separate empty directory,
create `a/b.cl` with this complete program:

<!-- sample: {"kind":"definition"} -->
```clojure
;; a/b.cl
(defn main [] (primitives/Pure 7))
```

`cranelisp --run a.b` resolves `a/b.cl` and exits `7`. A filesystem target such
as `cranelisp --run a/b.cl` also works, but chooses its project root from the
path argument. Use the [CLI target reference](../cli-reference.md#choosing-what-to-compile-the-target)
when selecting the root for a larger project.

## Child declarations and peer imports

`mod` loads a child beneath the declaring file's stem. In a separate project,
create these two files:

<!-- sample: {"kind":"illustrative","reason":"Two-file layout, not one REPL module; the following transcript loads and executes this exact app fixture"} -->
```clojure
;; app.cl
(mod helpers)
(defn main [] (primitives/Pure (app.helpers/answer)))

;; app/helpers.cl
(defn answer [] 7)
```

`cranelisp --run app` exits `7`. The child is `app.helpers`, and its canonical
qualified function name is `app.helpers/answer`. Within the parent, the short
child alias also permits `helpers/answer`.

You can also load that project from a REPL:

<!-- sample: {"kind":"repl","files":{"app.cl":"(mod helpers)\n(defn main [] (primitives/Pure (app.helpers/answer)))\n","app/helpers.cl":"(defn answer [] 7)\n"}} -->
```
user> (import [app []])
user> (app/main)
Executing IO…
:primitives/Int 7
```

`(mod helpers)` does **not** load a sibling `helpers.cl`. A sibling is a peer:
use `(import [helpers [answer]])` to bring its public function into scope.
Declaring a child loads it; importing names determines which bare spellings you
can use. The precise file lookup is [spec §8.2.5](../../spec/08-modules.md#825-file-resolution).

**Library-child limitation (ACT-1096):** a library module's declared child can
be replaced by a same-path project file or an earlier library search directory.
Keep those paths distinct today; a declared child's file belongs beside its
parent. How an independently resolved project child participates under a
library parent remains open as
[S124-Q14](../../spec/appendix-d-open-questions.md#s124-q14-can-a-project-file-be-a-child-of-a-library-resolved-parent).


`(mod- internal)` declares a private child, accessible within the declaring
module's subtree. The inline form `(mod child ...forms...)` creates a child file
and rewrites the declaration to `(mod child)`; use it when you want the REPL to
extract a new module for you, rather than as a permanent in-file namespace.
See [spec §8.2](../../spec/08-modules.md#82-module-declaration).

A child can import its parent through `super`. Avoid a cycle in which the parent
imports names from a child that imports `super`: the current compiler can hang
on this configuration. Test submodules do not need a reverse import for the
compiler's runner to discover them. See the [testing guide](testing.md) and the
[documented cycle limitation](../../spec/08-modules.md#838-super-import).

## Choose bare or qualified access

Open `cranelisp` in the original two-file project. These are REPL excerpts;
imports produce no result line, and the startup banner is omitted:

<!-- sample: {"kind":"repl","group":"mathx","files":{"mathx.cl":"(defn square [:Int x] (primitives/mul-i64 x x))\n(defn- secret [] 99)\n(deftype Shade Red Blue)\n"}} -->
```
user> (import [mathx [square]])
user> (square 7)
:primitives/Int 49
user> (mathx/square 8)
:primitives/Int 64
user> (import [(mathx mx) []])
user> (mx/square 9)
:primitives/Int 81
```

A selective import brings only its listed names into bare scope. A qualified
reference can load a module on demand without a bare import. An alias-only
import, as above, gives the module a shorter local name; it loads nothing until
used. `(import [mathx []])` imports nothing and registers no alias. One useful
null import is `(import [prelude []])`, which suppresses the implicit prelude.
See [spec §8.3](../../spec/08-modules.md#83-import).

To bring in every public name, use a glob. Continuing in the same session:

<!-- sample: {"kind":"repl","group":"mathx"} -->
```
user> (import [mathx [*]])
user> (square 5)
:primitives/Int 25
user> Shade.Red
:mathx/Shade mathx/Shade.Red ; deftype
```

A type import such as `[Shade]` gives access to `Shade.Red`; a member glob
`[Shade.*]` brings its constructors into bare scope. Importing members does not
bring the parent type into bare scope for annotations. The same distinction
applies to traits and their methods. See the [constructor guide](constructors.md),
[field-accessor guide](field-accessors.md), and
[accessibility table](../../spec/08-modules.md#8311-accessibility-after-import).

Renamed entries bind a local spelling, and selective member entries bind just
the requested constructor. In a fresh REPL in the same project:

<!-- sample: {"kind":"repl","files":{"mathx.cl":"(defn square [:Int x] (primitives/mul-i64 x x))\n(deftype Shade Red Blue)\n"}} -->
```
user> (import [mathx [(square sq) Shade.Blue]])
user> (sq 7)
:primitives/Int 49
user> Blue
:mathx/Shade mathx/Shade.Blue ; deftype
```

See [renamed imports](../../spec/08-modules.md#835-renamed-import) and
[member accessibility](../../spec/08-modules.md#8311-accessibility-after-import).

**Alias limitation (ACT-1082):** a missing member reached through an alias can
be reported against the alias instead of the real module; some REPL load orders
also refuse a valid aliased reference. Use the canonical module path when
investigating such a refusal.

## Keep internals private; re-export a public facade

`defn` defines a public function; `defn-` defines a private one. Private names do
not become accessible through either a glob or full module qualification. In
the original project, `(mathx/secret)` reports that `secret` is private to
`mathx`. The corresponding private definition forms include `deftype-`,
`deftrait-`, and `defmacro-`; see [spec §8.7](../../spec/08-modules.md#87-visibility).

Add `api.cl` to the original project, then open a fresh REPL there:

<!-- sample: {"kind":"definition","files":{"mathx.cl":"(defn square [:Int x] (primitives/mul-i64 x x))\n(defn- secret [] 99)\n(deftype Shade Red Blue)\n"}} -->
```clojure
;; api.cl
(export [mathx [square Shade]])
```

`(import [api [square]])` followed by `(square 7)` returns `49`. `export` makes
those names usable inside `api` and public to downstream importers. An ordinary
`import` keeps its local exposures private; importing something is not itself a
re-export. There is no need to import a name first and then export it.

An export mount adds a public module route. Replace `api.cl` with this file:

<!-- sample: {"kind":"definition","files":{"mathx.cl":"(defn square [:Int x] (primitives/mul-i64 x x))\n"}} -->
```clojure
;; api.cl
(export [(mathx math) [square]])
```

In a fresh REPL, load `api` through a public name before using its mount:

<!-- sample: {"kind":"repl","files":{"mathx.cl":"(defn square [:Int x] (primitives/mul-i64 x x))\n","api.cl":"(export [(mathx math) [square]])\n"}} -->
```
user> (import [api [square]])
user> (api.math/square 8)
:primitives/Int 64
```

The mount exposes the target module's public surface through `api.math`;
the name list also re-exports `square` directly from `api`. Renamed re-exports
use the same `(original local)` entry shape as imports. See
[spec §8.4](../../spec/08-modules.md#84-export).

**Mount-loading limitation (ACT-1079):** a qualified reference through a mount
can fail until its declaring module has loaded. An import of a real public
name, as above, loads the owner; an empty import does not. A chain of mounts
can require each owner to load first.

Distinct declarations can share a bare spelling. A call may select among them
by context and type; if it remains ambiguous, qualify the declaration you mean.
See [candidate selection](../../spec/08-modules.md#864-module-scope-candidate-registration) and the
[traits guide](traits.md#importing-trait-methods-a-method-reference-is-enough).

## Finding and editing modules

- The [CLI library-path reference](../cli-reference.md#where-cranelisp-looks-for-libraries-cranelisptoml)
  explains `CRANELISP_LIB`, `Cranelisp.toml` and the default `stdlib/` directory.
- `/imports` shows the current module's imports; `/exports mathx` shows a
  module's public surface. `/mod mathx` moves the REPL into that module.
- The [live-development guide](live-development.md) explains file watching,
  failed-save locks and persistence as you edit loaded modules.
- The [macros guide](macros.md) uses dependency modules for expansion helpers.
