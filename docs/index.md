# Cranelisp

Cranelisp is a statically typed, JIT-compiled Lisp built in Rust. It combines S-expression syntax with Hindley-Milner type inference, algebraic data types, traits with static dispatch, monadic IO, and a macro system — all compiled to native code through Cranelift.

```clojure
(defn fact [n]
  (if (= n 0)
    1
    (* n (fact (- n 1)))))

(defn main []
  (print (show (fact 10))))
```

No type annotations are needed — the compiler infers `fact :: (Fn [Int] Int)` and `main :: (Fn [] (IO Int))` automatically.

## What makes it interesting

**Full type inference with no runtime overhead.** Hindley-Milner inference means you rarely write types, but the compiler knows every type at every point. Traits dispatch statically — `(+ 1 2)` compiles to a single `iadd` instruction, not a method lookup.

**Clojure-style syntax, Haskell-style types.** S-expressions with square-bracket parameter lists, `defn`/`let`/`if`/`fn` as the core forms, and a prelude following Clojure naming conventions. Under the surface: polymorphic ADTs, constrained polymorphism via monomorphisation, and higher-kinded types for `Functor`.

**JIT-compiled through Cranelift.** Source goes through parsing, macro expansion, type checking, and Cranelift IR generation, then executes as native code. The same pipeline powers both batch execution and an interactive REPL.

**Self-documenting REPL.** Every symbol entered at the REPL produces useful feedback — its type, signature, or description. Special forms, operators, builtins, constructors, and user-defined names all respond with what they are and how to use them.

## Language features

- **Types**: `Int`, `Bool`, `String`, `Float`, `(Fn [params] ret)`, `(IO a)`, `(Option a)`, `(List a)`, `(Seq a)`, `(Vec a)`, user-defined ADTs
- **Algebraic data types**: product, sum, and enum forms with pattern matching and field accessors
- **Traits**: `Num`, `Eq`, `Ord`, `Display`, `Functor` with static dispatch; user-defined traits; operators are trait methods
- **Closures**: first-class functions with lambda capture and auto-currying
- **Macros**: `defmacro` with quasiquote/unquote/splice-unquote, compiled with Cranelift and run at expansion time
- **Monadic IO**: `do`/`pure`/`bind`/`bind!` for effect tracking; `main` must return `IO _`
- **Collections**: `Vec` with bracket syntax, linked `List`, lazy `Seq` with infinite sequence support; unified `map`/`filter`/`take`/`drop`/`reduce` API
- **Memory management**: reference counting with compiler-inserted inc/dec, per-type drop glue, deterministic deallocation
- **REPL**: introspection commands (`/sig`, `/doc`, `/type`, `/info`, `/source`, `/clif`, `/disasm`, `/time`, `/mem`)

## Design documents

These documents describe the design and implementation of each subsystem.

### Core pipeline

| Document | Description |
|----------|-------------|
| [Architecture](architecture.md) | Compilation pipeline from source to JIT execution, module responsibilities, data flow |
| [Syntax](syntax.md) | S-expression grammar, special forms, operators, type annotations, macros, builtins |
| [Type System](type-system.md) | Hindley-Milner inference (Algorithm W), unification, type schemes, inference rules |
| [Code Generation](codegen.md) | AST-to-Cranelift-IR mapping, JIT module lifecycle, builtin FFI, calling convention |

### Type system extensions

| Document | Description |
|----------|-------------|
| [Constrained Polymorphism](constrained-polymorphism.md) | Monomorphisation of trait-constrained functions at call sites |
| [Higher-Kinded Types](hkt.md) | Type constructor parameters in traits, enabling `Functor` over `Option`, `List`, etc. |
| [Traits](traits.md) | Trait declaration and implementation, operator dispatch, static resolution, mangled names |

### Data and control

| Document | Description |
|----------|-------------|
| [Algebraic Data Types](adt.md) | `deftype` for product/sum/enum types, `match` expressions, field accessors, runtime representation |
| [Closures](closures.md) | First-class functions, capture analysis, closure layout, calling convention |
| [Data Structures](data-structures.md) | Vec, List, Seq types; reference counting; copy-on-write; unified collection API |
| [IO](io.md) | Monadic IO design, `do`/`pure`/`bind`/`bind!`, eager execution, platform architecture |
| [Macros](macros.md) | `defmacro` system, quasiquoting, Sexp representation, expansion pipeline, prelude macros |

### Functions and dispatch

| Document | Description |
|----------|-------------|
| [Multi-Signature Functions](multi-sig.md) | Arity and type dispatch, auto-currying, unified collection API dispatch |
| [REPL Display](repl-display.md) | Symbol lookup, value formatting, slash commands, docstrings |

### Modules and names

| Document | Description |
|----------|-------------|
| [Modules](modules.md) | Module system design: file mapping, import/export, dot notation, per-module GOT |
| [Name Resolution](name-resolution.md) | How bare names resolve across modules: the two dictionaries, three-layer lookup, worked examples |

### Context

| Document | Description |
|----------|-------------|
| [Language Comparison](comparison.md) | How Cranelisp compares to Scheme, Common Lisp, Clojure, Carp, Roc, Rust, Zig, and Go |

## Getting started

Build and run with [just](https://github.com/casey/just):

```
just build          # compile
just test           # run all tests
just run FILE       # run a .cl source file
just hello          # run examples/hello.cl
just factorial      # run examples/factorial.cl
```

The `examples/` directory contains runnable programs demonstrating the language features.
