# Macros

## Overview & Motivation

Cranelisp's `defmacro` system lets macros be regular cranelisp functions that transform S-expressions before type checking. No separate interpreter is needed — macro functions are compiled with Cranelift and called during expansion, reusing the JIT's existing incremental compile-and-call pattern.

`list` and `bind!` are defined as prelude macros (not hardcoded parser sugar). New syntactic transformations like `->`, `cond`, or `case` can be added the same way — as macros in the prelude or user code.

Reference: Carp — a statically typed Lisp where macros expand before type checking.

## Pipeline Change

```
Source text
    |
    v
[Sexp Parser]       sexp.rs — balanced parens/brackets, atoms, strings
    |
    v
Sexp tree
    |
    v
[Macro Expander]    macro_expand.rs — calls JIT'd macro functions
    |
    v
Expanded Sexp
    |
    v
[AST Builder]       ast_builder.rs — Sexp → AST
    |
    v
AST → [TypeChecker] → [Codegen] → [JIT] → Execute
```

Macro functions are compiled incrementally as encountered, exactly like REPL definitions.

## Sexp Representation

### Rust-Side (Compiler Internals)

```rust
pub enum Sexp {
    Symbol(String, Span),
    Int(i64, Span),
    Float(f64, Span),
    Bool(bool, Span),
    Str(String, Span),          // `Str` avoids collision with std::String
    List(Vec<Sexp>, Span),      // (...)
    Bracket(Vec<Sexp>, Span),   // [...]
}
```

The `Bracket` variant stays distinct — brackets have context-dependent meaning resolved by the AST builder (param lists, field defs, vec literals, match arms).

Type annotations like `:Int` parse as `Symbol(":Int")` at the S-expr layer. The AST builder interprets the colon prefix.

### Cranelisp-Side (Macro Bodies)

The `Sexp` and `SList` types live in the synthetic `macros` module, compiler-seeded and immutable (like the `primitives` module). They are automatically available in all modules.

```clojure
;; In synthetic macros module (not user-modifiable):
(deftype (SList a)
  SNil
  (SCons [:a shead :(SList a) stail]))

(deftype Sexp
  (SexpSym [:String sname])
  (SexpInt [:Int sval])
  (SexpFloat [:Float sval])
  (SexpBool [:Bool sval])
  (SexpStr [:String sval])
  (SexpList [:(SList Sexp) sitems])
  (SexpBracket [:(SList Sexp) sitems]))
```

Both representations exist. Rust `Sexp` for the compiler pipeline, cranelisp `Sexp` ADT for macro function bodies. Marshal functions convert between them. `SList` is separate from the user-visible `List` type to decouple the macro system from user-modifiable standard library code.

## Two-Phase Parsing

**Phase 1** — `sexp.rs`: Text to Rust `Sexp`. A simple reader that handles:
- Balanced parentheses and brackets
- Atoms: integers, floats, booleans, strings, symbols (including `!` for `bind!`, `?` for `empty?`)
- Operators (`+`, `-`, `*`, `/`, `=`, `<`, `>`, `<=`, `>=`) with digit lookahead disambiguation
- Colon prefixes (`:Int` → `Symbol(":Int")`, bare `:` before `(` → separate `Symbol(":")`)
- `&` as standalone symbol (for variadic macro params)
- Line comments (`;`)
- Commas as whitespace
- Quasiquoting (`` ` ``, `~`, `~@`)

No knowledge of `defn`, `let`, `if`, etc. — the S-expr layer stays dumb.

**Phase 2** — `ast_builder.rs`: Rust `Sexp` to AST. Context-dependent interpretation that replaces the PEG grammar's AST construction logic. This is where `defn`, `let`, `if`, `match`, `deftype`, `deftrait`, `impl`, and `defmacro` are recognized and converted to AST nodes. (`do`, `pure`, `bind`, `bind!`, `list`, `vec` are macros/library functions, not AST builder special forms.)

## Macro Definition & Expansion

### Syntax

```clojure
(defmacro -> [x & forms]
  (sfold
    (fn [acc form]
      (match form
        [(SexpList items) (SexpList (SCons (shead items) (SCons acc (stail items))))
         _ (SexpList (slist form acc))]))
    x forms))
```

Macro parameters use `&` for variadic rest arguments, matching Clojure convention. Variadic params have type `(SList Sexp)`. Use `shead`/`stail` accessors or pattern matching (`SCons h t`) to destructure.

### How It Works

1. Sexp parser produces `(defmacro -> [x & forms] ...)` as raw Sexp
2. Macro expander recognizes `defmacro`:
   - Converts the body Sexp to AST (via AST builder)
   - Type-checks: macro function type must be `(Fn [(SList Sexp)] Sexp)` (receives args as SList, returns expanded form)
   - Compiles to Cranelift IR and JIT-finalizes
   - Registers the macro name in the `MacroEnv`
3. On encountering `(-> 5 inc (* 2))` later:
   - Marshal the args `(5, inc, (* 2))` to runtime Sexp ADT values using `sexp_to_runtime`
   - Call the JIT'd macro function
   - Marshal the result back to Rust `Sexp` using `runtime_to_sexp`
4. Re-expand the result (macros can expand to other macro calls)
5. Expansion limit (500 iterations) for infinite expansion detection

### Expansion Order

Single-pass, define before use. A `defmacro` can use any function or macro defined before it. No forward references for macros.

## Marshalling

Two Rust functions convert between Rust `Sexp` and runtime ADT values:

```rust
/// Allocate heap Sexp ADT values from a Rust Sexp tree.
fn sexp_to_runtime(sexp: &Sexp, jit: &mut Jit) -> i64

/// Read heap to reconstruct a Rust Sexp from a runtime ADT value.
fn runtime_to_sexp(val: i64) -> Sexp
```

These use the same heap layout as regular ADT values (`[tag, field0, field1, ...]`). The existing `format_adt_value` in the REPL is a reference for reading ADT values from heap.

## Quasiquoting

Quasiquoting avoids manual Sexp constructor calls:

| Syntax | Meaning |
|--------|---------|
| `` `expr `` | Quote — produce Sexp literal |
| `~expr` | Unquote — splice evaluated Sexp value |
| `~@expr` | Unquote-splicing — splice list of Sexp into surrounding list |

Parsed at the Sexp level as special forms:

- `` `(foo ~x ~@rest) `` parses as `(quasiquote (foo (unquote x) (unquote-splicing rest)))`
- Quasiquote expansion produces Sexp constructor calls using `SCons`/`SNil`: `(SexpList (SCons (SexpSym "foo") (SCons x (sconcat rest SNil))))`

### Example

Without quasiquote:
```clojure
(SexpList (slist (SexpSym "if") cond then-expr else-expr))
```

With quasiquote:
```clojure
`(if ~cond ~then-expr ~else-expr)
```

## Use Cases

### `list` — Variadic to Nested Cons

```clojure
(defmacro list [& elems]
  (sfold (fn [acc e] `(Cons ~e ~acc)) `Nil (sreverse elems)))
```

```clojure
(list 1 2 3)
;; expands to: (Cons 1 (Cons 2 (Cons 3 Nil)))
```

Note: `list` builds user-visible `List` values (using `Cons`/`Nil`), while `slist` builds `SList` values (using `SCons`/`SNil`) for use in Sexp constructors. The macro internals use `sfold`/`sreverse` which operate on `SList`.

### `bind!` — Monadic Bind Sugar

```clojure
(defmacro bind! [bindings body]
  (let [items (match bindings [(SexpBracket xs) xs])]
    (bind!-fold items body)))
```

Where `bind!-fold` is a prelude helper that recursively builds nested `(bind val (fn [name] ...))`:

```clojure
(defn bind!-fold [items body]
  (match items
    [SNil body
     (SCons name rest1)
       (match rest1
         [(SCons val rest)
            `(bind ~val (fn [~name] ~(bind!-fold rest body)))])]))
```

```clojure
(bind! [x (read-line)
       n (pure (parse-int x))]
  (print (show n)))

;; expands to:
(bind (read-line) (fn [x]
  (bind (pure (parse-int x)) (fn [n]
    (print (show n))))))
```

### `->` — Thread-First

```clojure
(defmacro -> [x & forms]
  (sfold
    (fn [acc form]
      (match form
        [(SexpList items) (SexpList (SCons (shead items) (SCons acc (stail items))))
         _ `(~form ~acc)]))
    x forms))
```

```clojure
(-> 5 inc (* 2))
;; expands to: (* (inc 5) 2)
```

### `->>` — Thread-Last

```clojure
(defmacro ->> [x & forms]
  (sfold
    (fn [acc form]
      (match form
        [(SexpList items) (SexpList (sconcat items (SCons acc SNil)))
         _ `(~form ~acc)]))
    x forms))
```

```clojure
(->> (list 1 2 3) (map inc) (reduce + 0))
;; expands to: (reduce + 0 (map inc (list 1 2 3)))
```

### `cond` — Multi-Way Conditional

```clojure
(defmacro cond [& clauses]
  (let [pairs (partition 2 clauses)]
    (list-reduce
      (fn [acc pair] `(if ~(first pair) ~(second pair) ~acc))
      `(panic "no matching cond clause")
      (reverse pairs))))
```

```clojure
(cond (< x 0) "neg"
      (= x 0) "zero"
      true     "pos")

;; expands to:
(if (< x 0) "neg"
  (if (= x 0) "zero"
    (if true "pos"
      (panic "no matching cond clause"))))
```

### `case` — Value Dispatch

```clojure
(defmacro case [expr & clauses]
  (let [pairs (partition 2 clauses)
        v (gensym "case")]
    `(let [~v ~expr]
       ~(list-reduce
          (fn [acc pair] `(if (= ~v ~(first pair)) ~(second pair) ~acc))
          `(panic "no matching case clause")
          (reverse pairs)))))
```

```clojure
(case color "red" 1 "green" 2 "blue" 3)

;; expands to:
(let [case_0 color]
  (if (= case_0 "red") 1
    (if (= case_0 "green") 2
      (if (= case_0 "blue") 3
        (panic "no matching case clause")))))
```

### `vec` — Prefix Vec Literal

```clojure
(defmacro vec [& elems]
  (SexpBracket elems))
```

```clojure
(vec 1 2 3)
;; expands to: [1 2 3]
;; AST builder produces VecLit
```

### Other Candidates

- `when` — `(when cond body)` expands to `(if cond body (pure 0))`
- `and`/`or` — short-circuiting via nested `if`
- `doto` — thread an object through side-effecting calls

## Bootstrapping Order

Prelude loading (`load_prelude`) uses two passes:

1. **Pass 1** — Register all type definitions (scan for `deftype`, build AST, register in typechecker)
2. **Pass 2** — Sequential compile with macro awareness:
   - `deftype` → skip (already registered)
   - `defmacro` → compile macro body (with expansion of earlier macros), register in `MacroEnv`
   - Everything else → expand through `MacroEnv`, build AST, typecheck, compile

This means `list` and `bind!` macros (defined at the end of `core.cl`) can use all prelude functions (`sreverse`, `sfold`, `bind!-fold`) and types (`Sexp`, `SList` from the synthetic `macros` module). The `compile_macro` function accepts an optional `MacroEnv` so that macro bodies can reference earlier macros (e.g. using `(slist ...)` inside a macro body).

A `defmacro` can use any function or macro defined before it. Macros cannot be forward-referenced.

## REPL Integration

- `MacroEnv` stored alongside `TypeChecker` and `Jit` in `ReplSession`
- `defmacro` at REPL registers and compiles immediately
- All subsequent input expanded before AST conversion
- `/expand <form>` REPL command shows macro expansion (debugging aid)

## Design Decisions

| Decision | Choice | Rationale |
|----------|--------|-----------|
| Macro body evaluation | JIT-compiled cranelisp | No second interpreter; macros use full language |
| Sexp representation | Cranelisp ADT + Rust enum | ADT for macro bodies, Rust enum for compiler internals |
| Quasiquoting | Yes | Manual Sexp constructor calls too verbose without it |
| Brackets in Sexp | Distinct `Bracket` variant | Context-dependent meaning resolved by AST builder |
| Hygiene | Unhygienic + `gensym` | Simpler than Scheme-style; matches Carp/Common Lisp |
| Expansion order | Single-pass, define before use | Simple, matches language's left-to-right evaluation |
| `vec` | Macro emitting `SexpBracket` | `(vec 1 2 3)` emits `[1 2 3]`; bracket form handled by AST builder |
| Span attribution | Macro call site | Expanded code points to where macro was invoked |

## Implementation Phases

| Phase | Feature | New/Modified Files |
|-------|---------|-------------------|
| **0** | **Rust `Sexp` type + S-expr parser** | **`src/sexp.rs` (done)** |
| **1** | **AST builder (Sexp to AST)** | **`src/ast_builder.rs` (done)** |
| **2** | **Wire as primary parser, keep PEG as reference** | **`src/batch.rs`, `src/repl/mod.rs`, tests (done)** |
| **3** | **Sexp ADT in synthetic `macros` module + marshal fns** | **`src/typechecker/primitives.rs`, `src/marshal.rs` (done)** |
| **4** | **`defmacro` + macro expander** | **`src/macro_expand.rs` (done)** |
| **5** | **Quasiquoting** | **`src/macro_expand.rs`, `examples/prelude.cl` (done)** |
| **6** | **Prelude macros (`list`, `bind!`), remove parser sugar** | **`prelude.cl`, `src/ast_builder.rs`, `src/batch.rs`, `src/repl/mod.rs`, `src/macro_expand.rs` (done)** |
| **7** | **New macros (`->`, `->>`, `cond`, `case`, `vec`), generalized operator parsing** | **`prelude.cl`, `src/sexp.rs` (done)** |
| **8** | **Remove PEG parser** | **`src/parser.rs` (deleted), imports updated (done)** |

## Limitations

- No hygienic macros (use `gensym` for introduced bindings)
- No macro-use-before-definition
- Error spans point to macro call site, not definition body
- Macro prelude must load before user macros (adds startup cost)
- No reader macros beyond quasiquote

## Future Extensions

- Hygienic macros
- Pattern-matching `defmacro` (multi-clause, like multi-sig `defn`)
- Reader macros
- `/expand` REPL debugger with step-by-step expansion
- Compile-time type access in macro bodies
