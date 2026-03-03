# Multi-Signature Functions and Auto-Currying

## Overview

A function can have multiple definitions with different parameter signatures. Variants may differ in arity, parameter types, or both. At each call site the compiler selects the matching variant by comparing argument types against the known signatures. Any function — single-sig or multi-sig — called with fewer arguments than it expects returns a closure that captures the applied arguments.

```clojure
(defn add
  ([x y] (+ x y))
  ([x y z] (+ x (+ y z))))

(add 1 2)                    ; dispatches to 2-arg variant → 3
(add 1 2 3)                  ; dispatches to 3-arg variant → 6
(let [f (add 10)] (f 5))     ; auto-curry of 2-arg variant → 15
```

## Syntax

### Multi-Signature `defn`

```clojure
(defn name
  ([param1 param2 ...] body)
  ([param1 param2 ...] body)
  ...)
```

Each variant is wrapped in parentheses with its own parameter list and body. Single-signature `defn` with a bare `[params]` is unchanged. The parser distinguishes the two forms by the first character after the name: `(` for multi-sig variants vs `[` for single-sig parameters.

### Restrictions

- A multi-sig name cannot be used as a bare value (e.g. bound in `let` or passed as an argument). The reference is ambiguous — the compiler reports an error. Use the function in a call, or use auto-curry with at least one argument.
- Two variants with identical parameter types are a duplicate-signature error, even if their bodies differ.

## Dispatch Mechanism

Dispatch follows the same deferred-resolution pattern as trait methods:

1. **Registration** — During `check_program`, each variant is assigned an internal name (`foo__v0`, `foo__v1`, ...) and registered in the type environment with fresh type variables.
2. **Inference** — Pass 2 checks each variant body, unifying parameter types with concrete types. Call sites referencing the base name record a pending resolution with their argument types and a fresh return-type variable.
3. **Mangling** — After Pass 2, each variant's concrete parameter types are read from the substitution map. The mangled name encodes the parameter types: `add$Int+Int`, `add$Int+Int+Int`, `choose$Int+Bool`.
4. **Resolution** — Pending call sites are matched against the mangled signatures. Exact arity + type match selects `SigDispatch`. Partial application selects `AutoCurry`. Ambiguity or no match is an error.

### Resolution Order

Overload resolution runs **before** trait method resolution. This ensures that return types from overloaded calls are concrete when the trait resolver inspects argument types for calls like `(show (add 1 2))`.

After selecting an exact match, `resolve_overloads` unifies parameter types with argument types (not just checks compatibility). This is important for binding type variables in the return type — e.g., `(map inc [1 2 3])` selects the Vec variant and unification binds the return type to `(Seq Int)` from the `(Vec Int)` input.

### Name Mangling

The mangled name is `name$T1+T2+...+Tn` where each `Ti` is the short name of the concrete parameter type:

| Type | Short Name |
|---|---|
| `Int` | `Int` |
| `Bool` | `Bool` |
| `String` | `String` |
| `Float` | `Float` |
| `Fn(...)` | `Fn` |
| `IO(...)` | `IO` |
| `ADT(name, args)` | `Name` (e.g., `Vec`, `List`, `Seq`) |

Zero-parameter variants mangle as `name$`.

## Auto-Currying

### Typing

When a call site provides fewer arguments than the callee expects, the type checker:

1. Unifies the provided arguments with the first N parameter types
2. Returns a function type over the remaining parameters
3. Records a pending `AutoCurry` resolution

```clojure
(defn add [x y] (+ x y))
; add : (Int, Int) -> Int

(add 10)
; applied: [Int]  remaining: [Int]
; result type: (Int) -> Int — a closure capturing 10
```

For single-sig functions the callee type is already known. For multi-sig functions the resolver narrows candidates by checking which variant's remaining arity matches the expected return type. For example, if context constrains the result to a 1-argument function, only the 2-argument variant (with 1 remaining) qualifies.

### Codegen

The `compile_auto_curry` method generates:

1. An anonymous **wrapper function** with signature `(env_ptr: i64, remaining_params...) -> i64`
2. The wrapper loads captured arguments from `env_ptr` at offsets `8, 16, ...`, combines them with the remaining parameters, and calls the target function
3. A **closure** `[wrapper_code_ptr, applied_arg0, applied_arg1, ...]` is heap-allocated

```
closure_ptr → [ wrapper_code_ptr | arg0 | arg1 | ... ]
               offset 0            +8     +16
```

At the call site the closure is returned as the expression result. When later called with the remaining arguments, the wrapper reconstructs the full argument list and dispatches to the target.

## `ResolvedCall` Enum

The resolution table maps expression spans to one of three call kinds:

```rust
pub enum ResolvedCall {
    TraitMethod { mangled_name: String },
    SigDispatch { mangled_name: String },
    AutoCurry { target_name: String, applied_count: usize, total_count: usize },
}
```

- **`TraitMethod`** — Trait dispatch (e.g. `show$Int`, `+$Float`).
- **`SigDispatch`** — Overloaded function dispatch to a mangled variant.
- **`AutoCurry`** — Partial application. `target_name` is the mangled name of the selected variant (or original name for single-sig). Codegen emits a closure capturing the applied arguments.

## Batch vs REPL

### Batch Mode

`check_program` processes `DefnMulti` items alongside regular `Defn` items. After resolution, `build_multi_defns` produces `Defn` items with mangled names. These are passed to `compile_and_run` as `extra_defns` so the codegen can declare and define them alongside regular functions.

### REPL Mode

`check_defn_multi` processes variants incrementally, returning a list of `(mangled_name, Defn, Scheme)` tuples. Each is compiled via `compile_defn` and gets its own slot in the function pointer table. Subsequent calls dispatch through the same overload resolution used in batch mode.

## Examples

### Different Arities

```clojure
(defn add
  ([x y] (+ x y))
  ([x y z] (+ x (+ y z))))

(add 1 2)       ; → 3  (dispatches to add$Int+Int)
(add 1 2 3)     ; → 6  (dispatches to add$Int+Int+Int)
```

### Type-Based Dispatch

```clojure
(defn choose
  ([x y] (+ x y))         ; y : Int
  ([x y] (if y x 0)))     ; y : Bool

(choose 10 20)     ; → 30  (dispatches to choose$Int+Int)
(choose 5 true)    ; → 5   (dispatches to choose$Int+Bool)
```

### Auto-Curry with Higher-Order Functions

```clojure
(defn add [x y] (+ x y))
(defn apply-fn [f x] (f x))

(apply-fn (add 10) 5)   ; → 15
; (add 10) returns a closure (fn [y] (+ 10 y))
; apply-fn calls it with 5
```

### Unified Collection API (Vec/List/Seq)

The multi-sig system enables a unified collection API that dispatches on container type. Each operation converts its input to a lazy Seq and delegates to the internal `lazy-*` functions:

```clojure
(defn map
  ([f v] (lazy-map f (vec-to-seq 0 v)))   ; v : (Vec a) → (Seq b)
  ([f l] (lazy-map f (list-to-seq l)))     ; l : (List a) → (Seq b)
  ([f s] (lazy-map f s)))                  ; s : (Seq a) → (Seq b)
```

ADT type constructors (`Vec`, `List`, `Seq`) have distinct mangled names, so the typechecker disambiguates at each call site:

```clojure
(to-list (map inc [1 2 3]))          ; Vec dispatch → map$Fn+Vec → (list 2 3 4)
(to-list (map inc (list 1 2 3)))     ; List dispatch → map$Fn+List → (list 2 3 4)
(to-list (take 3 (map inc (range-from 0)))) ; Seq dispatch → map$Fn+Seq → (list 1 2 3)
```

The same pattern applies to `filter`, `take`, `drop`, `reduce`, and `seq`.

## Limitations

- **Annotation syntax available**: variant parameter types can be annotated using `:Type param` syntax (e.g., `([:Int x :Bool y] ...)`), or inferred from bodies. See `docs/syntax.md`.
- **Bare multi-sig reference is an error**: you cannot pass a multi-sig function name as a value without at least one argument. Use auto-curry or a wrapping lambda instead.
- **No variadic dispatch**: each variant has a fixed parameter count. There is no rest-args mechanism.
- **Multi-sig + constrained polymorphism interaction**: multi-signature functions with constrained polymorphic variants are not yet supported. See `docs/constrained-polymorphism.md`.
- **Leaked closures**: auto-curry closures are heap-allocated and never freed, like all closures. See `docs/closures.md`.
