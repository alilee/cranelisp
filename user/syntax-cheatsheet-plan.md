# `/syntax` cheat-sheet

Use `/syntax` at the REPL when you need to recall a language form without
leaving the session. The command is available with or without the optional
agent feature.

```
user> /syntax
; core-language syntax topics:
;   defn  fn  match  traits  modules  ...
; Use /syntax <topic> for detail.

user> /syntax fn
TOPIC fn [core]
...
```

Bare `/syntax` is the topic index. `/syntax <topic>` prints a compact reference
with a form template and example. If the topic name is unknown, the REPL explains
that and prints the index again so you can choose a valid name.

The delivered topic content is the curated asset
[`src/syntax/cheatsheet.txt`](../src/syntax/cheatsheet.txt). It is a practical
syntax reference, not a second language specification; follow its links and the
normative [language specification](../spec/) for full rules and edge cases.

## What it covers

Topics cover core expressions and definitions (`defn`, `let`, `fn`, `match`,
patterns, annotations, vectors, recursion), types and constraints, declarations
(`deftype`, traits, `impl`), modules and imports, macros, and IO. Prelude syntax
such as `cond`, threading, `do`, and `bind!` is marked as prelude-provided rather
than core language.

## Macro authoring: reader annotations

This is a standard-library macro-authoring API, not a `/syntax` topic and not a
prelude export. A macro receives `:Type form` as one reader-folded value. Import
the helpers explicitly when the macro needs to inspect or discard that wrapper:

```clojure
(import [core.syntax [annotated? annotation unannotate]])
(import [primitives [Some None]])

(defmacro keep-subject [form]
  (if (annotated? form)
    (match (annotation form)
      [(Some _) (unannotate form)
       None form])
    form))

(keep-subject :Int 42)  ;; => 42
(keep-subject 42)       ;; => 42
```

`annotated?` recognises the wrapper, `annotation` returns its colon-stripped
type form as an `(Option Sexp)`, and `unannotate` returns the subject (or an
ordinary input unchanged). When you need both pieces, match the raw node instead:

```clojure
(defmacro keep-subject-raw [form]
  (match form
    [(macros/SexpAnnotated t f) f
     _ form]))
```

`SexpAnnotated` stores the annotation first and subject second; both are raw
`Sexp` values. The complete macro-facing representation is documented in
[`design/arch/annotated-sexp-node.md §3`](../design/arch/annotated-sexp-node.md).

## Related commands

- [`cli-reference.md`](cli-reference.md#repl-default--no-mode-flag) — REPL and
  command-line reference.
- `/search` finds public non-macro callable symbols; it is not a macro lookup.
- `/doc`, `/sig`, `/info`, `/list`, and `/imports` inspect what is already in
  your session.
