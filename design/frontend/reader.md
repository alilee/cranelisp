# Reader Design

Solution design for `cranelisp-frontend/src/reader.rs`: the source-to-Sexp parsing phase.

## Overview

The reader is the first phase of the frontend pipeline. It converts source text into `Vec<Sexp>`, a flat list of S-expression trees. Each `Sexp` node carries a `Span` for source location tracking.

```
Source text  --[reader]-->  Vec<Sexp>
```

## Architecture

### Parser Structure

Hand-written recursive descent parser using a `Reader` cursor struct that tracks byte position. No external parser library (no PEG, no nom) -- the grammar is simple enough for direct implementation.

### Token Precedence

Following spec 1.7, atoms are tried in order:
1. Float before integer (to capture decimal point)
2. Integer before operator (so `-3` parses as integer, not operator `-` followed by `3`)
3. Boolean before symbol (`true` is not a symbol)
4. String (double-quoted)
5. Special prefixes: `'`, `` ` ``, `~`, `~@`, `#(`, `$`, `%`, `&`
6. Colon-prefixed symbols (`:Int`, `:a`)
7. Regular symbols

### Delimiter Forms

- `(` ... `)` -> `Sexp::List`
- `[` ... `]` -> `Sexp::Bracket`

### Reader Macros

Syntactic sugar desugared at read time:
- `'x` -> `(quote x)`
- `` `x `` -> `(quasiquote x)`
- `~x` -> `(unquote x)`
- `~@x` -> `(unquote-splicing x)`
- `#(...)` -> `(anon-fn (...))`

### Whitespace

Commas are whitespace (Clojure convention). Comments run from `;` to end of line.

### String Parsing

Strings are double-quoted with backslash escapes: `\\`, `\"`, `\n`, `\t`, `\r`. Unterminated strings produce a `ParseError`.

## API Contract

```rust
#[must_use]
pub fn parse(source: &str) -> Result<Vec<Sexp>, CranelispError>
```

The `#[must_use]` annotation ensures callers handle the `Result`. Added in Ring 1 (deferred item M-5 from code review).

## Design Decisions

### Why hand-written parser?

The S-expression grammar is regular enough that a hand-written recursive descent parser is simpler and faster than pulling in a parser combinator or PEG library. It also gives full control over error messages and span tracking.

### Why `Span` on every node?

Every `Sexp` variant carries a `Span` to support precise error reporting in downstream phases. The AST builder, typechecker, and codegen all propagate spans for user-facing diagnostics.
