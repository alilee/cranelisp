# IO and Effect Tracking

## Motivation

Cranelisp aims to be a pure functional language with monadic IO and a pluggable runtime, inspired by Roc's platform/application model. Side effects must be tracked in the type system — a function that performs IO has a different type from a pure function. The Rust host acts as the "platform" that provides effect implementations; the language enforces that effectful code is explicitly marked.

## Strategy Comparison

Three main approaches to IO in functional languages:

**Lazy thunks (Haskell)**: `IO a` is a data structure describing future work; the runtime interprets it. Allocation-heavy, complex runtime, but enables reordering and optimization of effects.

**Eager execution with ADT wrapping (our approach)**: `IO a` is a real algebraic data type `(deftype (IO a) (IOVal [:a ioval]))`. Effects execute immediately when reached. The type system tracks IO propagation through inference. Simple, predictable, minimal overhead (one heap allocation per IO value).

**Task descriptions returned to platform (Roc)**: `main` returns `Task` values the platform interprets. The platform controls the execution loop. Requires heap allocation for Task values.

We chose eager execution with an ADT wrapper: it's a simple approach with minimal overhead (one heap allocation per IO result). The IO type is a compiler-seeded ADT in the `primitives` module, and `pure`/`bind`/`do` are standard library functions and macros — not compiler special forms. Roc-style Tasks remain a future option if we want the platform to control effect execution.

## Design

Four constructs: the `IO a` type, `do` for sequencing, `pure` for lifting, and `bind` for monadic extraction. `IO` is a compiler-seeded ADT; `pure` and `bind` are library functions in `lib/core/io.cl`; `do` and `bind!` are prelude macros in `lib/core/syntax.cl`.

### `IO a`

An algebraic data type seeded by the compiler in the `primitives` module:

```clojure
(deftype (IO a) (IOVal [:a ioval]))
```

`IO Int` means "an effectful computation that produces an Int." At runtime, an `IO a` value is a heap-allocated `IOVal` constructor: `[tag=0, value]`. Platform functions (`print`, `read-line`) return IOVal-wrapped results.

### `do`

```clojure
(do expr1 expr2 ... exprN)
```

A prelude macro that expands to nested `let` bindings:

```clojure
(do e1 e2 e3)
;; expands to:
(let [_ e1] (let [_ e2] e3))
```

Evaluates expressions left to right. Returns the value of the last expression. The block's type is the type of the last expression.

Any type is allowed in any position (permissive). This makes `do` a general expression-sequencing form usable in both pure and effectful contexts. The IO tracking comes from the types of the constituent expressions, not from `do` itself.

### `pure`

```clojure
(pure expr)
```

A library function (`lib/core/io.cl`) that wraps a value in an `IOVal` constructor. Type: `a -> IO a`.

Required when mixing pure and effectful branches in `if`:

```clojure
;; Without pure — TYPE ERROR: cannot unify IO Int with Int
(if (> x 0)
  (print (show x))  ; IO Int
  0)                 ; Int

;; With pure — OK
(if (> x 0)
  (print (show x))  ; IO Int
  (pure 0))         ; IO Int
```

### `bind`

```clojure
(bind io-expr continuation)
```

A library function (`lib/core/io.cl`) that pattern-matches the `IOVal` constructor to extract the inner value, then passes it to a continuation. Type: `IO a -> (a -> IO b) -> IO b`.

```clojure
;; Implementation:
(defn bind [io cont]
  (match io [(IOVal v) (cont v)]))
```

```clojure
;; bind extracts print's return value (0) and passes it to the continuation
(bind (print (show 42))
  (fn [result] (pure (+ result 1))))  ; result = 0, returns IO Int

;; Chaining multiple effects
(bind (print (show 10))
  (fn [_]
    (bind (print (show 20))
      (fn [_] (print (show 30))))))
```

### `bind!` — Monadic Bind Sugar

```clojure
(bind! [name io-expr]
  body)
```

A prelude macro (`lib/core/syntax.cl`) that desugars to nested `bind`/`fn` calls. Avoids deeply nested continuations when chaining multiple IO operations:

```clojure
;; With bind! — clear and flat
(bind! [line (read-line)]
  (print line))

;; Equivalent bind/fn — nested
(bind (read-line)
  (fn [line] (print line)))
```

Multiple bindings chain left to right:

```clojure
(defn main []
  (bind! [line (read-line)
         _ (print line)]
    (pure 0)))
```

### Effect typing

`print` has type `String -> IO Int`. `read-line` has type `(fn [] (IO String))`. Any function that calls an effectful builtin inherits an `IO` return type — effects propagate upward through the call graph automatically via type inference.

```clojure
(defn greet [x]       ; inferred: String -> IO Int
  (print x))

(defn greet-num [x]   ; inferred: Int -> IO Int
  (print (show x)))

(defn double-greet [x]  ; inferred: Int -> IO Int
  (do
    (print (show x))
    (print (show (+ x 1)))))
```

Pure functions remain pure:

```clojure
(defn add [x y]    ; inferred: Int -> Int -> Int
  (+ x y))
```

### `main`

`main` must return `IO _`. The Rust host is the platform — it calls `main`, receives the i64 result, and owns the process lifecycle.

```clojure
(defn main []
  (do
    (print (show 42))
    (print (show 100))))
```

## Architecture: Platform vs Language Builtins

The Rust host is split into two layers:

- **`src/platform.rs`** — the platform contract. Effect implementations visible to user code (`print`, `read-line`). These functions have `IO` return types. Swapping the platform swaps the effects — a test platform could capture output.
- **`src/intrinsics.rs`** — language internals. Machinery invisible to user code (`alloc` for closure and string heap allocation). No `IO` types — these are implementation details.

```
┌─────────────────────────────┐
│  User code (cranelisp)      │  (defn main [] (print 42))
├─────────────────────────────┤
│  Platform (src/platform.rs) │  print : String -> IO Int, read-line : () -> IO String
├─────────────────────────────┤
│  Language (src/intrinsics.rs)│  alloc : (internal, not in type env)
└─────────────────────────────┘
```

## Execution model

Effects execute eagerly. When the JIT'd code reaches `(print "hello")`, it calls the Rust `print_string` function immediately. The result is wrapped in an `IOVal` constructor (a real heap-allocated ADT value), not a lazy thunk or data structure describing future work.

This differs from Roc's model where the application returns a `Task` description to the platform for interpretation. The eager model is simpler but means the host cannot inspect, reorder, or batch effects. The IOVal wrapper adds one heap allocation per IO result.

## Pluggable runtime

Builtins are provided by the Rust host via `JITBuilder::symbol`. Swapping the host swaps the effect implementations — a test host could capture output instead of printing, a web host could redirect to a DOM node. The type-level contract (`print : String -> IO Int`) is the interface between application and platform.

## Future extensions

| Feature | Prerequisite | Description |
|---|---|---|
| Lazy `Task` values | Closures + heap | Return effect descriptions to the host instead of executing eagerly |
| `Task ok err` | ADTs | Effects that carry error types, enabling typed error handling |
| Formal platform declarations | Module system | Platform explicitly declares which effects it provides |
