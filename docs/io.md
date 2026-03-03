# IO and Effect Tracking

## Motivation

Cranelisp aims to be a pure functional language with monadic IO and a pluggable runtime, inspired by Roc's platform/application model. Side effects must be tracked in the type system — a function that performs IO has a different type from a pure function. The Rust host acts as the "platform" that provides effect implementations; the language enforces that effectful code is explicitly marked.

## Design

Four constructs: the `IO a` type, `do` for sequencing, `pure` for lifting, and `bind` for monadic chaining. `IO` is a compiler-seeded ADT with three constructors (`Pure`, `Effect`, `Bind`); `pure` is a library function in `lib/core/io.cl`; `bind` is an inline primitive (constructs `Bind` nodes in Cranelift IR); `do` and `bind!` are prelude macros in `lib/core/syntax.cl`.

### `IO a`

An algebraic data type seeded by the compiler in the `primitives` module with three constructors:

```clojure
(deftype (IO a)
  (Pure [:a ioval])       ; tag=0: completed value
  (Effect [:a thunk])     ; tag=1: deferred effect (opaque Rust closure pointer)
  (Bind ...))             ; tag=2: chain (internal — not user-constructable)
```

`IO Int` means "a deferred computation that will produce an Int when forced." At runtime:

- `Pure`: heap `[tag=0, value]` — 16 bytes
- `Effect`: heap `[tag=1, thunk_ptr, resource_token]` — 24 bytes (thunk_ptr → double-boxed `Box<Box<dyn FnOnce() -> i64>>`; resource_token=0 means unrestricted)
- `Bind`: heap `[tag=2, inner_io_ptr, cont_closure_ptr]` — 24 bytes
- `Par`: heap `[tag=3, count, io0, io1, ...]` — internal compiler node; see below

The `Bind` and `Par` constructors are marked `internal` — they appear in `/info IO` for documentation but cannot be constructed or pattern-matched by user code. `Bind` has an existential type (`exists b. IO b * (b -> IO a)`) that HM inference cannot express. `Par` is inserted by the compiler into `bind!` chains when data-independent `Commutative` effects are detected; see `docs/concurrency.md` for the automatic IO scheduling design.

### `do`

```clojure
(do expr1 expr2 ... exprN)
```

A prelude macro that expands to nested `bind` calls:

```clojure
(do e1 e2 e3)
;; expands to:
(bind e1 (fn [_] (bind e2 (fn [_] e3))))
```

`do` is **IO-specific** — all expressions must have type `IO _`. For pure sequencing, use `let [_ expr1] expr2`.

### `pure`

```clojure
(pure expr)
```

A library function (`lib/core/io.cl`) that wraps a value in a `Pure` constructor. Type: `a -> IO a`.

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

An inline primitive that constructs a `Bind` node in the IO task tree. Type: `IO a -> (a -> IO b) -> IO b`.

At compile time, `bind` generates Cranelift IR that allocates a 24-byte Bind node: `[tag=2, io_ptr, cont_ptr]`. No execution happens — the chain is only interpreted when the trampoline forces it.

```clojure
;; bind chains IO actions — nothing executes until forced
(bind (print (show 42))
  (fn [result] (pure (+ result 1))))

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

A prelude macro (`lib/core/syntax.cl`) that desugars to nested `bind`/`fn` calls. Avoids deeply nested continuations:

```clojure
;; With bind! — clear and flat
(bind! [line (read-line)]
  (print line))

;; Equivalent bind/fn — nested
(bind (read-line)
  (fn [line] (print line)))
```

### Effect typing

`print` has type `String -> IO Int`. `read-line` has type `(fn [] (IO String))`. Any function that calls an effectful builtin inherits an `IO` return type — effects propagate upward through the call graph automatically via type inference.

```clojure
(defn greet [x]       ; inferred: String -> IO Int
  (print x))

(defn greet-num [x]   ; inferred: Int -> IO Int
  (print (show x)))
```

Pure functions remain pure:

```clojure
(defn add [x y]    ; inferred: Int -> Int -> Int
  (+ x y))
```

### `main`

`main` must return `IO _`. The Rust host calls `main`, receives the IO task tree, forces it via the trampoline, and owns the process lifecycle.

```clojure
(defn main []
  (do
    (print (show 42))
    (print (show 100))))
```

## Architecture: Platform vs Language Builtins

The Rust host is split into two layers:

- **Platform DLLs** (`platforms/stdio/`, `platforms/test-capture/`) — effect implementations visible to user code (`print`, `read-line`). These functions construct `Effect` nodes containing opaque Rust closures. The closures capture the actual side effect and execute only when the trampoline forces them.
- **`src/intrinsics.rs`** — language internals. Machinery invisible to user code (`alloc` for heap allocation, `IoTask`/`Continuation` for the trampoline). No user-visible `IO` types.

```
┌─────────────────────────────────┐
│  User code (cranelisp)          │  (defn main [] (print 42))
├─────────────────────────────────┤
│  Platform DLLs                  │  print : String -> IO Int (returns Effect node)
├─────────────────────────────────┤
│  Trampoline (src/intrinsics.rs) │  IoTask.run() forces the IO tree
├─────────────────────────────────┤
│  Runtime (cranelisp-runtime)    │  alloc, free, panic
└─────────────────────────────────┘
```

## Execution model: Task + Trampoline

Effects are **deferred**. When JIT'd code reaches `(print "hello")`, the platform DLL constructs an `Effect` node containing a Rust closure that captures the side effect. Nothing is printed yet. The IO task tree accumulates as `bind` chains `Bind` nodes, `pure` creates `Pure` nodes, and platform functions create `Effect` nodes.

When the program returns from `main`, the runtime forces the tree via a flat **trampoline** loop:

```rust
pub fn run(self) -> i64 {
    let mut cont_stack: Vec<Continuation> = Vec::new();
    let mut current = self;
    loop {
        match current.tag() {
            Pure => {
                let val = current.pure_val();
                match cont_stack.pop() {
                    Some(cont) => current = cont.call(val),
                    None => return val,
                }
            }
            Effect => {
                let result = current.run_effect();  // executes the side effect
                match cont_stack.pop() {
                    Some(cont) => current = cont.call(result),
                    None => return result,
                }
            }
            Bind => {
                let (inner, cont) = current.split_bind();
                cont_stack.push(cont);
                current = inner;  // loop back, no recursion
            }
            Par => {
                // compiler-inserted for Commutative, data-independent bind! pairs
                let results = current.par_ios()
                    .into_par_iter()
                    .map(|io| io.run())  // each branch gets its own trampoline
                    .collect::<Vec<_>>();
                match cont_stack.pop() {
                    Some(cont) => current = cont.call(results_ptr(results)),
                    None => return results_ptr(results),
                }
            }
        }
    }
}
```

The `Bind` case pushes the continuation and loops — no recursion, O(1) call stack depth. IO loops run indefinitely without stack growth.

### Safety encapsulation

The trampoline uses two newtype wrappers that push all `unsafe` pointer operations to accessor methods:

- `IoTask(i64)` — opaque IO task tree pointer with safe `tag()`, `pure_val()`, `run_effect()`, `split_bind()` accessors
- `Continuation(i64)` — cranelisp closure wrapper with a safe `call(val)` method

The trampoline loop body is entirely safe Rust.

### Effect thunks

Platform DLLs create `Effect` nodes containing **double-boxed Rust closures** (`Box<Box<dyn FnOnce() -> i64>>`). The double-boxing produces a thin pointer (single `i64`) that fits in the Effect node. Platform authors write natural `move || { ... }` closures:

```rust
pub fn print_string(s: CLString) -> CLIO<CLInt> {
    CLIO::effect(move || {
        println!("{}", s.as_str());
        CLInt(0)
    })
}
```

The `CLIO::effect()` method handles boxing, allocation, and tag setup. The trampoline's `run_effect()` unboxes and calls the thunk via `call_effect_thunk()`.

### REPL forcing

In the REPL, IO expressions are forced immediately after evaluation so the user sees output interactively. The REPL checks the result type — if it's `IO _`, it forces via the trampoline before displaying the inner value.

### Batch mode

In batch mode (`cranelisp --run`), `call_main()` checks main's return type. If main returns `IO`, the result is forced via the trampoline. Non-IO main functions return their value directly.

### Standalone executables

The exe startup stub (`src/exe.rs`) calls `cranelisp_run_io()` (an `extern "C"` trampoline entry point in the runtime bundle) to force main's IO tree before calling `exit()`.

## Pluggable runtime

All IO effects come from dynamically-loaded platform DLLs via `(platform name)`. Swapping the platform swaps the effect implementations — a test platform captures output instead of printing, a web platform could redirect to a DOM node. The type-level contract (`print : String -> IO Int`) is the interface between application and platform.

## Future extensions

| Feature | Prerequisite | Description |
|---|---|---|
| Automatic IO scheduling | `SchedulingClass` in platform ABI | Compiler analyses `bind!` chains; inserts `Par` nodes for data-independent `Commutative` effects automatically; see `docs/concurrency.md` |
| `Task ok err` | Task model | Effects carrying error types, enabling typed error handling |
| Formal platform declarations | Module system | Platform explicitly declares which effects it provides |
