# Reader

Interior design for `crates/cranelisp-frontend/src/reader.rs` — source text to
`Vec<Sexp>`.

## Structure

A hand-written recursive-descent parser over a `Reader` cursor that tracks a byte
position. There is no external parser library: the S-expression grammar is
regular enough that direct implementation is simpler and faster than a
combinator or PEG dependency, and it gives full control over diagnostics and
span tracking.

Every `Sexp` node carries a `Span`. Downstream stages — AST builder, typecheck,
codegen — propagate spans for user-facing diagnostics, and a node without a real
span degrades every error that reaches it, so span assignment is not optional
anywhere in the reader.

## Token precedence

Atoms are tried in a fixed order (spec §1.7), and the order is load-bearing:

1. float before integer, so the decimal point is captured;
2. integer before operator, so `-3` is an integer rather than `-` applied to `3`;
3. boolean before symbol, so `true` is not a symbol;
4. string (double-quoted, with `\\`, `\"`, `\n`, `\t`, `\r` escapes; an
   unterminated string is a located parse error);
5. the prefix sigils `'`, `` ` ``, `~`, `~@`, `#(`, `$`, `%`, `&`;
6. colon-introduced annotations;
7. plain symbols.

`(` … `)` reads as `Sexp::List` and `[` … `]` as `Sexp::Bracket`. Commas are
whitespace (Clojure convention) and `;` runs to end of line.

## Reader macros

Sigils desugar at read time into ordinary list forms, so nothing downstream has
to know the surface spelling:

| Written | Read as |
|---|---|
| `'x` | `(quote x)` |
| `` `x `` | `(quasiquote x)` |
| `~x` | `(unquote x)` |
| `~@x` | `(unquote-splicing x)` |
| `#(…)` | `(anon-fn (…))` |

The quote family is then desugared into constructor applications by the AST-entry
fold (`quasiquote-fold.md`), not by the reader.

`:` is the annotation introducer and is **not** a sigil producing a list form.
`read_colon_prefix` reads the annotation half and the following subject and
constructs one `Sexp::Annotated` node; the fold is recursive, so every position
that can hold a form can hold an annotated form. `s116-syntax-and-annotation.md`
§2 owns that judgment, including the located rejection when the introducer is
followed by `)`, `]` or EOF.

## Qualified and dotted names

`/` and `.` are structurally significant inside a symbol, and the reader is the
only place where adjacency and emptiness are both known. A qualified name
requires **both halves non-empty**; a dangling qualifier (`foo/`, `:foo/`,
`:a.b/`, `/bar`) is a located error at the reader rather than a silent
degradation, while a bare `/` remains the division operator. The single dotted
module-path lexer is `consume_dotted_module_path`, used by both the symbol and
the annotation paths so the two cannot diverge. `enforcement-matrices.md` §3
states the rule and its fences.

A dotted *name* (`Box.v`, `Option.Some`, `Num.+`) reads as one
`Sexp::Symbol("Box.v")` and is transported verbatim — the reader is
member-case-agnostic and never splits or rewrites it. Resolution of the dotted
form is typecheck's. This is distinct from a dotted *module path* (`core.io/pure`),
which the reader only continues collecting across dots when a `/` follows.

## Comment preservation

`parse` discards comments; `parse_preserving_comments` emits them as
`Sexp::Comment(text, span)` nodes. The flag lives on the `Reader` and defaults to
off, so the compiler pipeline pays nothing: no filtering pass, no allocation, and
no downstream stage that can encounter a comment node. `/source` and the REPL
pretty-printer are the consumers that need the preserving mode (repl/spec.md
§10.3).

**Stored text.** The `;` marker and exactly one following space are stripped; a
bare `;` stores `""`. Interior alignment after that one space is content and is
preserved. The trailing newline is never included. The span covers the `;`
through the last non-newline character. `format_flat` re-emits the canonical
`; text` form, so a comment round-trips.

**Position.** Comment nodes appear where they occurred: as siblings inside `List`
and `Bracket` children, among top-level forms, and at the end of the vector for
end-of-file comments. The reader does not distinguish standalone from inline
comments — both are `Sexp::Comment` positioned by source location. This means a
comment inside a form appears between the forms it separated, which is what makes
faithful re-rendering possible.

**Isolation.** The AST builder, typechecker and backend must never encounter a
`Sexp::Comment`. The primary mechanism is that the pipeline uses `parse`. The
builder additionally skips comment nodes where it iterates children, as
defence-in-depth against a future caller that feeds preserving output into the
pipeline; adding the variant already forces exhaustive-match updates, so the skip
arms cost nothing extra. Typecheck and backend never see `Sexp` at all, so the
isolation boundary is the Sexp-to-AST translation and nowhere else.

The leading comment block has a second, separate consumer: the module preamble
(`module-preamble.md`), which re-scans the raw source head rather than reading
the comment stream, because the blank-line boundary rule is not recoverable from
the stream.

## Cross-references

- `spec/01-lexical.md` §1.4.5, §1.7 — colon-prefixed symbols and atom precedence.
- `design/arch/interfaces.md` §"Reader Output" — the `Sexp` carrier and its variants.
- `design/frontend/enforcement-matrices.md` §3 — the dangling-qualifier rejects.
- `design/frontend/s116-syntax-and-annotation.md` §2 — the read-time annotation fold.
