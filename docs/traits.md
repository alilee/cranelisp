# Traits and Static Dispatch

## Overview

Cranelisp uses traits for ad-hoc polymorphism. A trait declares method signatures parameterized over a `Self` type. Implementations provide concrete method bodies for specific types. At compile time, the typechecker resolves each trait method call to a specific implementation based on the inferred type — there is no runtime dispatch.

```clojure
(deftrait Greet
  (hello [Self] String))

(impl Greet Int
  (hello [x] (show x)))

(hello 42)  ; resolves to hello$Int at compile time
```

## Builtin Traits

Five traits are defined in `src/prelude.cl`. Three are "operator traits" that power the arithmetic and comparison syntax; one provides string conversion; one is a higher-kinded type trait.

### Display

Converts a value to its string representation.

| Method | Signature | Description |
|---|---|---|
| `show` | `a -> String` | Convert to string |

Impls: Int, Bool, String, Float. `show` is callable by name in user code.

```clojure
(show 42)       ; "42"
(show true)     ; "true"
(show "hello")  ; "hello"
(show 3.14)     ; "3.14"
```

### Num

Arithmetic operations. Accessed through operator syntax.

| Method | Signature | Operator |
|---|---|---|
| `+` | `a -> a -> a` | `(+ x y)` |
| `-` | `a -> a -> a` | `(- x y)` |
| `*` | `a -> a -> a` | `(* x y)` |
| `/` | `a -> a -> a` | `(/ x y)` |

Impls: Int, Float.

```clojure
(+ 1 2)      ; Num.+ on Int → 3
(* 3.0 4.0)  ; Num.* on Float → 12.0
```

### Eq

Equality comparison.

| Method | Signature | Operator |
|---|---|---|
| `=` | `a -> a -> Bool` | `(= x y)` |

Impls: Int, Float.

```clojure
(= 1 1)      ; Eq.= on Int → true
(= 1.0 2.0)  ; Eq.= on Float → false
```

### Ord

Ordering comparisons.

| Method | Signature | Operator |
|---|---|---|
| `<` | `a -> a -> Bool` | `(< x y)` |
| `>` | `a -> a -> Bool` | `(> x y)` |
| `<=` | `a -> a -> Bool` | `(<= x y)` |
| `>=` | `a -> a -> Bool` | `(>= x y)` |

Impls: Int, Float.

```clojure
(< 1 2)      ; Ord.< on Int → true
(>= 5.0 5.0) ; Ord.>= on Float → true
```

### Functor (Higher-Kinded)

Maps a function over a type constructor. This is an HKT trait — the type parameter `f` is a type constructor (kind `* -> *`), not a concrete type.

| Method | Signature | Description |
|---|---|---|
| `fmap` | `(a -> b) -> f a -> f b` | Apply function inside a container |

Impls: Option, List.

```clojure
(fmap inc (Some 5))        ; => (Some 6)
(fmap inc (list 1 2 3))    ; => (list 2 3 4)
(fmap inc None)            ; => None
```

See `docs/hkt.md` for full details on higher-kinded type traits.

## User-Defined Traits

### Declaration

```clojure
(deftrait TraitName
  (method1 [Self] ReturnType)
  (method2 [Self OtherType] ReturnType))
```

`Self` is a placeholder that gets replaced with the implementing type. Method signatures use type expressions: `Self`, `Int`, `Bool`, `String`, `(IO Type)`, `(fn [Params...] Ret)`.

Higher-kinded traits use lowercase type constructor parameters instead of `Self`:

```clojure
(deftrait (TraitName f)
  (method1 [(Fn [a] b) (f a)] (f b)))
```

Here `f` is a type constructor variable — implementations provide a concrete type constructor like `Option` or `List`. See `docs/hkt.md`.

### Implementation

```clojure
(impl TraitName TargetType
  (defn method1 [x] body1)
  (defn method2 [x y] body2))
```

Each method body is type-checked with parameter types derived from the trait signature, with `Self` replaced by `TargetType`.

For HKT traits, the target is a bare type constructor name:

```clojure
(impl Functor Option
  (defn fmap [f opt]
    (match opt
      [None None
       (Some x) (Some (f x))])))
```

### Example

```clojure
(deftrait Describable
  (describe [Self] String))

(impl Describable Int
  (defn describe [x] (show x)))

(impl Describable Bool
  (defn describe [x] (if x "yes" "no")))

(print (describe 42))      ; prints "42"
(print (describe true))    ; prints "yes"
```

## Type Inference

### Display Methods (show)

When the typechecker sees `(show x)`:

1. Look up `show` in the type environment → `forall a. a -> String`
2. Instantiate with a fresh variable → `t0 -> String`
3. Infer `x`'s type, unify with `t0`
4. Record a pending resolution: `(span, "show", t0)`

After all bodies are checked, `resolve_methods` applies the substitution to find the concrete type of `t0` and looks up the matching impl.

### Operator Methods (+, =, <, ...)

Operators are registered in the type environment via `deftrait` declarations in the prelude and `register_trait`. When the typechecker sees `(+ x y)`, it is parsed as `Apply(Var("+"), [x, y])` and handled uniformly:

1. Look up `+` in the environment → its polymorphic type from the Num trait
2. Instantiate with fresh variables
3. Infer operand types and unify
4. Record a pending resolution: `(span, "+", operand_type)`

### Resolution Order

Resolution happens in three phases after type inference:

1. **Operator methods** (`resolve_operator_methods`): Resolves Num/Eq/Ord methods. When the operand type is still a type variable and multiple impls exist, constraints are recorded for constrained polymorphism (see `docs/constrained-polymorphism.md`).

2. **Overload dispatch** (`resolve_overloads`): Resolves multi-signature function calls using concrete parameter types.

3. **Remaining methods** (`resolve_methods`): Resolves Display and user trait methods. By this point, return types from overloaded calls are concrete.

This ordering is critical. Operator resolution must come first because multi-signature functions that use arithmetic (e.g., `([x y] (+ x y))`) need concrete parameter types for signature matching.

### Mangled Names

Each resolved method call maps to a mangled name: `method$Type`. Examples:

| Call | Resolved Name |
|---|---|
| `(show 42)` | `show$Int` |
| `(show true)` | `show$Bool` |
| `(show 3.14)` | `show$Float` |
| `(+ 1 2)` | `+$Int` |
| `(+ 1.0 2.0)` | `+$Float` |
| `(= 1 1)` | `=$Int` |
| `(< 3 4)` | `<$Int` |
| `(fmap inc (Some 5))` | `fmap$Option` |
| `(fmap inc (list 1 2))` | `fmap$List` |

The `MethodResolutions` table maps AST spans to `ResolvedCall` entries carrying the mangled name.

## Code Generation

### Builtin Trait Methods

**Display (show)**: `show` impls are FFI functions registered via `JITBuilder::symbol`. `show$Int` maps to `int-to-string`, etc. Calls compile to `call` instructions.

**Operator traits (Num, Eq, Ord)**: Int and Float impls compile to inline Cranelift instructions via `compile_inline_primitive` — no function call overhead:

| Method (Int) | Cranelift IR |
|---|---|
| `+$Int` | `iadd(lhs, rhs)` |
| `-$Int` | `isub(lhs, rhs)` |
| `*$Int` | `imul(lhs, rhs)` |
| `/$Int` | `sdiv(lhs, rhs)` |
| `=$Int` | `icmp(Equal, lhs, rhs)` + `uextend.i64` |
| `<$Int` | `icmp(SignedLessThan, lhs, rhs)` + `uextend.i64` |
| `>$Int` | `icmp(SignedGreaterThan, lhs, rhs)` + `uextend.i64` |
| `<=$Int` | `icmp(SignedLessThanOrEqual, lhs, rhs)` + `uextend.i64` |
| `>=$Int` | `icmp(SignedGreaterThanOrEqual, lhs, rhs)` + `uextend.i64` |

| Method (Float) | Cranelift IR |
|---|---|
| `+$Float` | `bitcast` + `fadd` + `bitcast` |
| `-$Float` | `bitcast` + `fsub` + `bitcast` |
| `*$Float` | `bitcast` + `fmul` + `bitcast` |
| `/$Float` | `bitcast` + `fdiv` + `bitcast` |
| `=$Float` | `bitcast` + `fcmp(Equal)` + `uextend.i64` |
| `<$Float` | `bitcast` + `fcmp(LessThan)` + `uextend.i64` |
| `>$Float` | `bitcast` + `fcmp(GreaterThan)` + `uextend.i64` |
| `<=$Float` | `bitcast` + `fcmp(LessThanOrEqual)` + `uextend.i64` |
| `>=$Float` | `bitcast` + `fcmp(GreaterThanOrEqual)` + `uextend.i64` |

### User-Defined Trait Methods

User trait method bodies compile as regular functions with mangled names. For example, `(impl Describable Int (defn describe [x] ...))` compiles a function named `describe$Int`. Calls resolve to `compile_direct_call("describe$Int", ...)`.

## REPL Behavior

### Operator Descriptions

Typing an operator at the REPL displays its trait-based type:

```
cranelisp> +
+ :: Num a => (fn [a a] a)
cranelisp> =
= :: Eq a => (fn [a a] Bool)
cranelisp> <
< :: Ord a => (fn [a a] Bool)
```

### Trait Descriptions

Typing a trait name displays its declaration:

```
cranelisp> Display
Display :: trait (show :: (fn [a] String))
```

### Method Descriptions

Typing a trait method name displays its polymorphic type and trait:

```
cranelisp> show
show :: Display a => (fn [a] String)
```

## Design Decisions

**Operators are in the type environment.** Operator symbols (`+`, `-`, `=`, `<`, etc.) are registered via `register_trait` from the prelude's `deftrait` declarations. They are looked up like any other function during inference via `Apply(Var(op), args)`.

**Zero-cost Int and Float operations.** Builtin arithmetic compiles to the same Cranelift instructions as hardcoded operations. The `compile_inline_primitive` helper routes codegen to direct IR emission rather than a function call. Performance is identical to having no trait system.

**Operators as first-class values.** `(let [f +] (f 3 4))` works — the operator is wrapped in a closure via `compile_builtin_as_closure`, using operator wrapper functions from `primitives/int.rs` and `primitives/float.rs`.

## Limitations

- **Name collision risk.** User functions named `show` will shadow the Display trait method in the type environment, potentially causing unexpected behavior. See KNOWN_ISSUES.md.
- **HKT + constrained polymorphism.** Cannot write `(defn map-inc [xs] (fmap inc xs))` as a generic function over all Functors. See `docs/hkt.md`.

## Future Extensions

| Feature | Description |
|---|---|
| Default method implementations | Derive `<=` from `<` and `=`, etc. |
| Deriving | Auto-generate Eq/Ord impls for data types |
| Monad/Applicative | HKT traits for sequencing and composition (see `docs/hkt.md`) |
