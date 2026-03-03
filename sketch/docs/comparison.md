# Language Comparison

How Cranelisp compares to other languages it draws inspiration from or shares design space with.

## Summary Table

| Feature | Cranelisp | Scheme | Common Lisp | Clojure | Carp | Roc | Rust | Zig | Go |
|---|---|---|---|---|---|---|---|---|---|
| **Syntax** | S-expr | S-expr | S-expr | S-expr | S-expr | ML-like | C-like | C-like | C-like |
| **Typing** | Static, inferred | Dynamic | Dynamic | Dynamic | Static, inferred | Static, inferred | Static, annotated | Static, annotated | Static, annotated |
| **Type inference** | Hindley-Milner | None | None | None | Hindley-Milner | Hindley-Milner | Local | None | None |
| **Compilation** | JIT (Cranelift) | Interpreter/AOT | AOT/Interpreter | JVM bytecode | AOT (C backend) | AOT (LLVM) | AOT (LLVM) | AOT (LLVM) | AOT (Go toolchain) |
| **Memory** | Ref counting | GC | GC | GC (JVM) | Ref counting + borrow | Ref counting | Ownership + borrow | Manual + arena | GC |
| **Effects** | Monadic IO | Unrestricted | Unrestricted | Unrestricted | Unrestricted | Managed (platform) | Unrestricted | Unrestricted | Unrestricted |
| **Polymorphism** | Traits + HKT | Ad hoc | CLOS | Protocols | Interfaces | Abilities | Traits + HKT | Comptime | Interfaces |
| **Dispatch** | Static (monomorphised) | Dynamic | Dynamic (CLOS) | Dynamic (protocols) | Static | Static | Static (+ dyn) | Static | Dynamic (interfaces) |
| **Macros** | `defmacro` (unhygienic) | `syntax-rules` (hygienic) | `defmacro` (unhygienic) | Reader + `defmacro` | `defmacro` (unhygienic) | None | `macro_rules!` + proc | Comptime | None |
| **Mutability** | Immutable values | Mutable (`set!`) | Mutable | Immutable (persistent) | Mutable (owned) | Immutable | Mutable (owned) | Mutable | Mutable |
| **Concurrency** | None (yet) | Threads/continuations | Threads | STM, agents, core.async | None | Tasks | async/Send+Sync | async + threads | Goroutines + channels |

## Lisps

### Scheme

Scheme is the minimal Lisp — a small specification with lexical scoping, tail-call optimisation, continuations, and hygienic macros.

**Shared ground.** Both languages use S-expression syntax with prefix notation. Both treat functions as first-class values with lexical closure. Both favour recursion over iteration.

**Where Cranelisp diverges.** Cranelisp adds static types with full Hindley-Milner inference — Scheme is dynamically typed. Cranelisp compiles to native code via Cranelift JIT; most Scheme implementations are interpreters or bytecode VMs (with notable exceptions like Chez Scheme and Gambit). Cranelisp tracks side effects in the type system via monadic IO; Scheme allows effects anywhere. Cranelisp uses unhygienic macros with `gensym`; Scheme's `syntax-rules` provides hygienic transformation. Cranelisp uses reference counting for memory; Scheme requires tail-call optimisation and typically uses tracing GC.

**What Scheme has that Cranelisp lacks.** Tail-call optimisation (essential for idiomatic Scheme), continuations (`call/cc`), a mature standard library (R7RS), and decades of pedagogical material. Scheme's minimalism makes it easy to implement and reason about formally.

### Common Lisp

Common Lisp is the industrial Lisp — a large specification with CLOS (the Common Lisp Object System), multiple dispatch, condition/restart error handling, and a powerful macro system.

**Shared ground.** Both use S-expression syntax and unhygienic `defmacro` with quasiquoting. Both support algebraic-style data modelling (CL via `defstruct` and CLOS). Both aim to compile to efficient native code.

**Where Cranelisp diverges.** Cranelisp is statically typed with full inference; CL is dynamically typed (with optional type declarations for optimisation hints). Cranelisp uses traits with static dispatch; CL uses CLOS with runtime multiple dispatch. Cranelisp's type system enforces effect tracking; CL allows side effects freely. Cranelisp uses Clojure-style syntax conventions (square-bracket params, `defn`); CL uses its own conventions (`defun`, no square brackets). Cranelisp has no condition/restart system.

**What Common Lisp has that Cranelisp lacks.** CLOS with multiple dispatch, the condition/restart system (more powerful than exceptions), optional typing with `declare`, compiler macros, reader macros, `loop` and `format`, and a vast ecosystem of libraries. SBCL compiles CL to highly optimised native code competitive with C.

### Clojure

Clojure is a modern Lisp on the JVM — immutable persistent data structures, software transactional memory, and a focus on practical concurrent programming.

**Shared ground.** Cranelisp deliberately follows Clojure conventions: square-bracket parameter lists, `defn`/`let`/`if`/`fn` as core forms, `defmacro` with quasiquoting, and Clojure-inspired standard library naming (`map`, `filter`, `reduce`, `take`, `drop`, `show`). Both languages default to immutable values. Cranelisp's Vec literal `[1 2 3]` mirrors Clojure's vector syntax.

**Where Cranelisp diverges.** Cranelisp is statically typed with Hindley-Milner inference; Clojure is dynamically typed (with optional `core.spec` and `core.typed`). Cranelisp compiles to native code via Cranelift; Clojure targets the JVM. Cranelisp uses reference counting; Clojure relies on JVM garbage collection. Cranelisp tracks effects via monadic IO; Clojure allows side effects anywhere. Cranelisp uses algebraic data types with pattern matching; Clojure uses maps and multimethods. Cranelisp dispatches traits statically; Clojure protocols dispatch dynamically on the first argument.

**What Clojure has that Cranelisp lacks.** Persistent data structures (HAMTs, RRB-trees) with structural sharing, the `core.async` concurrency library, transducers, metadata, namespaced keywords, destructuring in binding forms, REPL-driven interactive development with a mature tooling ecosystem, and the entire Java ecosystem via interop. Clojure's emphasis on "data as maps" and spec-based validation is a fundamentally different approach to data modelling than Cranelisp's algebraic data types.

### Carp

Carp is Cranelisp's closest relative — a statically typed Lisp with type inference, compiled ahead of time via a C backend, with reference counting and borrow checking instead of garbage collection.

**Shared ground.** Both are statically typed Lisps with Hindley-Milner type inference. Both use reference counting for memory management without a GC. Both use unhygienic `defmacro`. Both monomorphise polymorphic functions. Both aim for zero-overhead abstractions compiled to native code. Cranelisp's macro system design explicitly references Carp.

**Where Cranelisp diverges.** Cranelisp compiles via Cranelift JIT; Carp compiles to C. Cranelisp tracks effects via monadic IO; Carp allows effects anywhere. Cranelisp has algebraic data types with pattern matching; Carp uses `deftype` for structs and sumtypes with a different syntax. Cranelisp has higher-kinded types (Functor); Carp does not. Cranelisp has a REPL with JIT; Carp's REPL recompiles through C. Cranelisp uses Clojure syntax conventions; Carp has its own conventions (though also Clojure-influenced).

**What Carp has that Cranelisp lacks.** Borrow checking (Carp analyses ownership to avoid unnecessary copies), a mature C FFI, interop with C libraries, and a more complete standard library. Carp's memory management is more developed — it statically determines when copies are needed rather than relying on runtime reference count checks for copy-on-write.

## Functional

### Roc

Roc is a pure functional language with the platform/application model — applications describe effects as data, and a host platform interprets them.

**Shared ground.** Both are statically typed with Hindley-Milner inference. Both use reference counting instead of GC. Both compile to native code (Roc via LLVM, Cranelisp via Cranelift). Both have algebraic data types. Cranelisp's IO design document explicitly discusses Roc's Task model as an alternative approach.

**Where Cranelisp diverges.** Cranelisp uses S-expression syntax; Roc uses ML-style syntax. Cranelisp executes effects eagerly (IO is a real ADT wrapping results, not a lazy thunk); Roc returns Task descriptions to the platform for interpretation. Cranelisp has macros; Roc has none. Cranelisp uses traits with monomorphisation; Roc uses abilities. Cranelisp has higher-kinded types; Roc does not (by design — Roc avoids HKT complexity). Cranelisp's platform concept is implicit (Rust host provides FFI builtins); Roc's platform/application split is a first-class language feature.

**What Roc has that Cranelisp lacks.** The platform/application model (formal separation of effects from logic), tag unions (anonymous, structural), record types (structural, not nominal), `when`/`is` pattern matching with exhaustiveness checking, the `!` suffix for effectful functions, a complete compiler pipeline with optimisations, and a growing ecosystem. Roc's design philosophy of "no footguns" leads to deliberate omissions (no HKT, no typeclasses, no macros) that Cranelisp includes.

## Conventional

### Rust

Rust is a systems language with ownership, borrowing, and lifetimes — zero-cost abstractions with guaranteed memory safety and no GC.

**Shared ground.** Cranelisp is implemented in Rust and inherits some design philosophy: traits with static dispatch, monomorphisation of generics, algebraic data types with pattern matching (`enum` in Rust, `deftype` in Cranelisp), and expression-oriented design. Both use Cranelift (Rust's `codegen_cranelift` backend, Cranelisp's JIT). Both aim for zero-overhead polymorphism.

**Where Cranelisp diverges.** Cranelisp uses S-expression syntax; Rust uses C-style syntax with significant additions. Cranelisp has full type inference (no annotations needed); Rust requires type annotations on function signatures. Cranelisp uses reference counting; Rust uses ownership with compile-time borrow checking. Cranelisp is garbage-collected (via RC) and values are immutable; Rust gives fine-grained control over mutability and allocation. Cranelisp is purely functional with monadic IO; Rust is multi-paradigm with unrestricted mutation. Cranelisp has macros operating on S-expressions; Rust has `macro_rules!` and procedural macros operating on token streams.

**What Rust has that Cranelisp lacks.** The ownership/borrowing system (compile-time memory safety without runtime cost), async/await, a sophisticated module system, a massive ecosystem (crates.io), error handling via `Result`/`?`, lifetimes, const generics, comprehensive tooling (cargo, rustfmt, clippy), and production-grade optimisation. Rust's type system is more expressive (GATs, trait objects, `dyn`, associated types) but requires more annotations.

### Zig

Zig is a systems language focused on simplicity — no hidden control flow, no hidden allocations, comptime evaluation, and explicit error handling.

**Shared ground.** Both aim to produce efficient native code. Both avoid hidden runtime costs (Cranelisp's trait dispatch is static; Zig avoids hidden allocators and control flow). Both are relatively young languages with opinionated designs.

**Where Cranelisp diverges.** Cranelisp uses S-expression syntax with Hindley-Milner inference; Zig uses C-like syntax with explicit types. Cranelisp is purely functional; Zig is imperative with manual memory management. Cranelisp has GC (via RC); Zig requires explicit allocators. Cranelisp has closures and first-class functions; Zig has function pointers but closures require explicit capture. Cranelisp has a macro system; Zig uses comptime (compile-time evaluation of regular code) instead of macros.

**What Zig has that Cranelisp lacks.** Comptime (compile-time code execution using the same language, not a separate macro language), explicit allocator passing, `errdefer`, packed structs, C interop without bindings, a safety-first debug mode, and cross-compilation to many targets. Zig's philosophy of "no hidden behaviour" is more extreme than Cranelisp's — even `+` can't silently overflow.

### Go

Go is a pragmatic language for networked services — garbage collected, structurally typed, with goroutines and channels for concurrency.

**Shared ground.** Both aim for fast compilation. Both have simple type systems relative to their peers (Cranelisp avoids Haskell's complexity; Go avoids Rust's complexity). Both use structural conventions for common patterns (Cranelisp's trait dispatch is syntactically invisible; Go's interfaces are satisfied implicitly).

**Where Cranelisp diverges.** Cranelisp uses S-expression syntax with full type inference; Go uses C-like syntax with type annotations everywhere. Cranelisp is purely functional with immutable values; Go is imperative with mutable state. Cranelisp uses reference counting; Go uses a concurrent tracing GC. Cranelisp has algebraic data types with pattern matching; Go uses structs and interfaces. Cranelisp has monadic IO for effect tracking; Go allows effects anywhere. Cranelisp has macros and closures with capture; Go has closures but no macros or generics-level metaprogramming.

**What Go has that Cranelisp lacks.** Goroutines and channels (lightweight concurrency), a comprehensive standard library, a mature toolchain (go build, go test, go vet), structural interface satisfaction, fast compilation of large codebases, and widespread industry adoption. Go's simplicity is a different kind from Cranelisp's — Go omits type inference, ADTs, and generics (until recently) in favour of explicit, readable code.

## Design Space

Cranelisp occupies an unusual position: it combines Lisp syntax and macros with an ML-family type system and systems-language memory management. The closest point in design space is Carp, which makes similar choices. The key differentiators from Carp are monadic IO, higher-kinded types, and JIT compilation via Cranelift.

Compared to the Lisps, Cranelisp trades dynamic flexibility for static guarantees — types are checked at compile time, effects are tracked, and dispatch is resolved before execution. Compared to ML-family languages (which share the type system heritage), Cranelisp trades conventional syntax for S-expression homoiconicity and macro power. Compared to systems languages, Cranelisp trades manual memory control for automatic reference counting with deterministic deallocation.
