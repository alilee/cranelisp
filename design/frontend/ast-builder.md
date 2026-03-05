# AST Builder Design

Solution design for `cranelisp-frontend/src/ast_builder.rs`: the Sexp-to-Expr/TopLevel translation phase.

## Overview

The AST builder is the second phase of the frontend pipeline. It receives `Vec<Sexp>` from the reader and produces `Vec<TopLevel>` (batch mode) or `ReplInput` (REPL mode). It validates structural well-formedness, desugars syntactic patterns, and produces typed AST nodes.

```
Source text  --[reader]-->  Vec<Sexp>  --[ast_builder]-->  Vec<TopLevel> / ReplInput
```

## Architecture

### Entry Points

- `build_program(sexps, expander) -> Result<Program>`: batch mode. Each sexp must be a top-level form.
- `build_repl_input(sexp, expander) -> Result<ReplInput>`: REPL mode. Accepts top-level forms and bare expressions.

Both delegate to shared builders via `build_top_level` and `build_expr`.

### Ring-Gated Form Acceptance

Forms are accepted or rejected based on the current ring. Ring 0 provides the core expression forms (let, if, fn/lambda, match, apply, literals, annotations). Later rings add new forms by replacing rejection arms with production code.

| Ring | Forms added |
|------|------------|
| 0 | `defn`, `deftype` (enum-only at first, full fields/type params in code), `let`, `if`, `fn`/`lambda`, `match`, `apply`, int/float/bool literals, type annotations |
| 1 | `StringLit` (string literals as expressions) |
| 2 | `deftrait`, `impl` |
| 3 | `quote`, `quasiquote`, `unquote`, `unquote-splicing`, `anon-fn`, `vec` |
| 4 | `trace`, `run-tests`, `par-let` |

### Docstring Detection

Docstrings are detected positionally by `extract_optional_docstring(children, start)`. A `Sexp::Str` at position `start` in a top-level form's children is consumed as a docstring. This is unambiguous because:

1. Docstrings can only appear at specific positions in `defn` and `deftype` (after the name, before the parameter list or constructors).
2. String literals in expression position are handled by `build_expr`, which is called for the body -- never for the docstring position.
3. String-valued let bindings like `(let [s "hello"] s)` go through `build_expr` for binding values, not through docstring extraction.

### Type Expression Building

`build_type_expr` translates Sexp forms in annotation position to `TypeExpr`:

- Bare uppercase symbol -> `TypeExpr::Named` (e.g., `Int`, `Bool`)
- Bare lowercase symbol -> `TypeExpr::TypeVar` (e.g., `a`, `b`)
- `self` -> `TypeExpr::SelfType`
- `(Fn [params] ret)` -> `TypeExpr::FnType`
- `(Name args...)` -> `TypeExpr::Applied` (e.g., `(Option Int)`, `(Map String Int)`)

Annotation consumption uses `try_consume_annotation` which handles:
- `:Name` -> simple named type or type var
- `: (compound)` -> compound type via `build_type_expr`

### Deftype Desugaring

`desugar_type_def` handles three syntactic forms:

1. **Enum**: `(deftype Color Red Green Blue)` -> one nullary constructor per variant
2. **Product**: `(deftype Point [:Int x :Int y])` -> single constructor with typed fields
3. **Sum**: `(deftype (Option a) None (Some [:a val]))` -> multiple constructors, some with fields
4. **Shortcut**: `(deftype Pair [first second])` -> bare field names get sequential type vars (a, b, c, ...)

### Pattern Building

`build_pattern` produces `Pattern` variants from Sexp in match arms:

- `_` -> `Pattern::Wildcard`
- Uppercase-starting symbol -> `Pattern::Constructor` (nullary)
- Lowercase-starting symbol -> `Pattern::Var`
- `(Constructor bindings...)` -> `Pattern::Constructor` with field bindings

## Ring 1 Changes

### StringLit Acceptance

Ring 1 replaced the `Sexp::Str` rejection in `build_expr` with `Expr::StringLit { value, span }` emission. This was a single-arm change: the match arm for `Sexp::Str` now clones the string value and wraps it in the `StringLit` variant instead of returning an error.

The existing `extract_optional_docstring` needed no changes -- it correctly distinguishes docstrings (positional, in top-level forms) from string-valued expressions (in `build_expr` scope).

### No Structural Changes for ADTs or Closures

The full ADT syntax (type parameters, data constructors with fields, shortcut syntax) and constructor patterns with bindings were implemented structurally in Ring 0, even though the typechecker and backend could not yet handle them. Ring 1 required no frontend changes for these features -- the AST builder already produces the correct nodes. The typechecker and backend are responsible for the new semantics.

## Design Decisions

### Why complete AST in Ring 0?

The frontend builds the full structural AST for all rings, rejecting only expression forms that require later-ring semantics. This means:
- `deftype` with fields and type params: fully desugared in Ring 0
- Constructor patterns with bindings: fully built in Ring 0
- `TypeExpr::Applied`: fully parsed in Ring 0

This avoids structural changes to the AST builder in later rings, keeping it stable. Only expression-level gates (like `Sexp::Str` rejection) change ring-by-ring.

### Macro Expansion via Trait

The `MacroExpander` trait is defined in `cranelisp-types` for dependency inversion. The AST builder consults the expander at call sites, allowing Ring 0 to use `NoOpExpander` while later rings provide real expansion. The expander is checked before treating a list form as a function application.
