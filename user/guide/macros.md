# Macros — transform source before it runs

A macro receives source forms and returns a source form for the compiler to
expand and typecheck. Use a function for ordinary computation; use a macro when
you need to control the shape of the code, such as introducing a binding.
The [module guide](modules.md) introduces the dependency files used below.

The runnable groups on this page use a fresh REPL with the default prelude.
Each definition block precedes its uses. Result comments show expression values;
normal definition feedback is omitted. REPL transcripts are excerpts with the
startup banner and timing prefix omitted.

## Return a source form

`defmacro` takes a name, parameters and a body that returns `macros/Sexp`.
Quote (`'`) turns source into data, so `'7` is the source form for the integer
literal, rather than the integer result of evaluating it:

<!-- sample: {"kind":"definition","group":"macros"} -->
```clojure
(defmacro always-seven [] '7)
(always-seven)                              ; => 7
```

The call expands to `7`, then the compiler checks and evaluates that expansion.
An ordinary macro parameter receives a `Sexp`, not the value of its argument.
`macros/Sexp` represents literals, symbols, lists, brackets and annotations;
`macros/SList` represents sequences of these forms. It is separate from the
standard library's ordinary `List`.
See [spec §9.1–§9.2](../../spec/09-macros.md#91-sexp-data-model).

Constructors can also build source explicitly, for example
`(macros/SexpInt 7)`. Use qualified constructor names, or import them with
`(import [macros [*]])`. Quote and quasiquote generate qualified constructor
references for you, so simple templates do not need that import.

## Quasiquote fills a template

A backtick quotes a template; `~` unquotes a computed form into it. Continuing in
the same session:

<!-- sample: {"kind":"definition","group":"macros"} -->
```clojure
(defmacro twice [x] `(primitives/add-i64 ~x ~x))
(twice 21)                                  ; => 42
```

Both occurrences of `~x` insert the argument's source. If that source computes
something, the expanded code contains it twice. A macro does not automatically
arrange one evaluation.

`~@` splices a sequence of forms into a surrounding list or bracket. A rest
parameter receives the remaining arguments as an `(SList Sexp)`:

<!-- sample: {"kind":"definition","group":"macros"} -->
```clojure
(defmacro call [f & args] `(~f ~@args))
(call primitives/add-i64 3 4)                ; => 7
```

Here `f` receives the symbol `primitives/add-i64`, and `args` holds the source
forms `3` and `4`. Splicing inserts two arguments into the call. `&args` and
`& args` are equivalent spellings. See
[quasiquote](../../spec/09-macros.md#94-quasiquote) and
[macro parameters](../../spec/09-macros.md#922-parameters).

## Match bracket parameters

A bracket parameter destructures the source bracket passed by the caller. This
example introduces a binding around the supplied body:

<!-- sample: {"kind":"definition","group":"macros"} -->
```clojure
(defmacro with-value [[name value] body]
  `(let [~name ~value] ~body))
(with-value [n 8] (primitives/add-i64 n 1))   ; => 9
```

The bracket needs two elements for this clause. `(with-value [n] n)` produces a
compile-time macro error saying no clause matches; the REPL remains usable.
This is a rejected source shape, rather than a runtime panic.

A macro can provide several clauses, selected in definition order by argument
count and bracket shape. A bracket pattern can itself end in `& rest` to collect
its remaining elements. See [spec §9.2.6–§9.2.7](../../spec/09-macros.md#926-multi-clause-macros)
for the matching rules.

## Introduce temporary names carefully

When a template needs a private temporary binding, use an auto-gensym name
ending in `#`. Within one template, repeated occurrences get the same generated
name; another expansion gets a different one:

<!-- sample: {"kind":"definition","group":"macros"} -->
```clojure
(defmacro once [x]
  `(let [value# ~x] (primitives/add-i64 value# value#)))
(let [value 100] (once 4))                    ; => 8
```

The generated binding does not capture the caller's `value`. Ordinary names
introduced by templates can still capture names; auto-gensym is not full macro
hygiene. Use canonical module qualification for external functions, as these
examples do. See [spec §9.8](../../spec/09-macros.md#98-hygiene).

## Put expansion helpers in dependencies

Define a macro before using it in the same module. This also applies within one
REPL `begin` input. A successfully installed macro is available to later forms;
a failed definition does not install a new macro.

A non-macro helper called **during expansion** belongs in a dependency module.
Putting a `defn` above the macro in the same file does not make that helper
available at expansion time. Create this separate three-file project:

<!-- sample: {"kind":"definition"} -->
```clojure
;; syntax-tools.cl
(defn quoted-seven [] '7)
```

<!-- sample: {"kind":"definition","files":{"syntax-tools.cl":"(defn quoted-seven [] '7)\n","forms.cl":"(import [syntax-tools [quoted-seven]])\n(defmacro seven [] (quoted-seven))\n"}} -->
```clojure
;; forms.cl
(import [syntax-tools [quoted-seven]])
(defmacro seven [] (quoted-seven))
```

<!-- sample: {"kind":"definition","files":{"syntax-tools.cl":"(defn quoted-seven [] '7)\n","forms.cl":"(import [syntax-tools [quoted-seven]])\n(defmacro seven [] (quoted-seven))\n"}} -->
```clojure
;; app.cl
(import [forms [seven]])
(defn main [] (primitives/Pure (seven)))
```

Run `cranelisp --run app` from that directory: it prints nothing and exits `7`.
The files are separate modules: `forms` depends on `syntax-tools`, and `app`
depends on `forms`. Qualified macro calls such as `(forms/seven)` also reach
dependency modules. See [availability and order](../../spec/09-macros.md#934-macro-availability-and-definition-order)
and [bootstrapping](../../spec/09-macros.md#912-bootstrapping-order).

## Preserve reader annotations

The reader folds `:Type form` into **one** annotated source value before the
macro receives it. A macro that transports its argument unchanged preserves
that wrapper automatically. Back in the original REPL group:

<!-- sample: {"kind":"definition","group":"macros"} -->
```clojure
(defmacro hold [form] form)
(hold :Int 42)                              ; => 42
```

`hold` receives one argument, not separate `:Int` and `42` arguments. Structural
matching needs to account for `macros/SexpAnnotated`, whose first payload is
the annotation without its colon and whose second payload is the subject.
Both payloads are source forms.

The focused [reader-annotation reference](syntax-command.md#macro-authoring-reader-annotations)
shows `core.syntax/annotated?`, `annotation` and `unannotate`, plus raw matching.
Use those helpers when you want to inspect or remove an annotation; keep the
wrapper when you only intend to forward the form. See
[spec §9.2.2](../../spec/09-macros.md#922-parameters).

## Inspect expansion and edit future uses

In the original REPL group, `/expand` (short form `/e`) shows expanded source
without evaluating it:

<!-- sample: {"kind":"repl","group":"macros"} -->
```
user> /expand (twice 21)
(primitives/add-i64 21 21)
user> (defmacro amount [] '7)
:(Fn [] macros/Sexp) user/amount ; defmacro
user> (defn saved [] (amount))
:(Fn [] primitives/Int) user/saved ; defn
user> (defmacro amount [] '9)
:(Fn [] macros/Sexp) user/amount ; defmacro
user> (saved)
:primitives/Int 7
user> (amount)
:primitives/Int 9
```

Macro replacement affects **future expansions**. `saved` keeps the old expansion
until you redefine or reload it. `/sig`, `/doc`, `/info` and `/list` inspect
installed macros. See [live development](live-development.md#other-definitions)
and [REPL §18.4](../../repl/spec/18-redefinition.md#184-macro-redefinition).

A panic while executing an expansion ends the **compiler process**, including
the REPL; there is no panic-capture wrapper. Validate a caller's source shape
through clauses and ordinary compile-time diagnostics where possible. The
runtime rule is [spec §12.7](../../spec/12-runtime.md#127-error-model).

The standard prelude supplies macros such as `def`, `cond` and threading forms.
`def` still has an [unresolved application boundary](live-development.md#the-def-macros-current-boundary);
do not infer that it behaves like a core value-binding special form. For a
quick syntax reminder, use [`/syntax`](syntax-command.md); for precise macro
contracts, use [spec §9](../../spec/09-macros.md).
