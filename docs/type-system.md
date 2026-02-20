# Type System

## Types

Cranelisp has the following types:

| Type | Description | Runtime representation |
|---|---|---|
| `Int` | 64-bit signed integer | i64 |
| `Bool` | Boolean | i64 (0 = false, 1 = true) |
| `String` | UTF-8 string | i64 (heap pointer to `[i64 len][u8 bytes...]`) |
| `Float` | 64-bit IEEE 754 float | i64 (f64 bits stored via bitcast) |
| `Fn(params, ret)` | Function type | i64 (pointer to closure struct) |
| `IO(a)` | Effectful computation | ADT: heap `[tag=0, value]` (compiler-seeded `(deftype (IO a) (IOVal [:a ioval]))`) |
| `ADT(name, args)` | Algebraic data type | nullary ctors = bare i64 tag; data ctors = heap `[tag, fields...]` |
| `TyConApp(id, args)` | Type constructor variable applied to args | Resolves to ADT during inference |
| `Var(id)` | Type variable | Resolved during inference |

All values are `i64` at runtime. Function values are pointers to heap-allocated closure structs (see `docs/closures.md`). `IO` is a real ADT — `IO a` values are heap-allocated `IOVal` constructors, like any other single-constructor ADT.

## Type Inference: Algorithm W

Cranelisp uses Hindley-Milner type inference (Algorithm W). All types can be inferred without annotations, but optional type annotations are available to constrain types or add trait requirements. See `docs/syntax.md` for annotation syntax.

### Core Operations

1. **`fresh_var()`** — Generate a new unique type variable `Var(id)`.

2. **`unify(a, b)`** — Make two types equal by adding to the substitution map:
   - `Int = Int`, `Bool = Bool`, `String = String`, `Float = Float` → success
   - `Var(id) = T` → record `id ↦ T` (with occurs check)
   - `Fn(p1, r1) = Fn(p2, r2)` → unify params pairwise, then unify returns
   - `ADT(n1, args1) = ADT(n2, args2)` → names must match, unify args pairwise (includes `IO` which is `ADT("IO", [a])`)
   - `TyConApp(f, args1) = ADT(name, args2)` → bind `f ↦ ADT(name, [])`, unify args pairwise
   - Otherwise → type error

3. **`apply(subst, ty)`** — Walk a type, replacing any `Var(id)` that has a mapping in the substitution.

4. **`instantiate(scheme)`** — Replace a scheme's quantified variables with fresh variables. Used when referencing a polymorphic function.

5. **`generalize(ty)`** — Quantify over type variables not free in the environment. Produces a `Scheme`.

### Two-Pass Checking

To support forward references and recursion:

**Pass 1** — Register all `defn` names with fresh type variables:
```
fact : Fn([t0], t1)    -- params and return are unknowns
main : Fn([], t2)
```

**Pass 2** — Check each function body:
- Add parameter types to the environment
- Infer the body type
- Unify the body type with the return type variable
- The substitution map accumulates constraints

After both passes, generalize all function types.

### Inference Rules by Expression

| Expression | Rule |
|---|---|
| `IntLit` | → `Int` |
| `BoolLit` | → `Bool` |
| `FloatLit` | → `Float` |
| `StringLit` | → `String` |
| `Var(name)` | Lookup in env, instantiate scheme |
| `Apply(Var("+"), [a, b])` | Num trait: fresh var `t`, unify both operands with `t`, result `t` |
| `Apply(Var("="), [a, b])` | Eq trait: fresh var `t`, unify both operands with `t`, result `Bool` |
| `Apply(Var("<"), [a, b])` | Ord trait: fresh var `t`, unify both operands with `t`, result `Bool` |
| `Let([x e1], body)` | Infer `e1`, bind `x` to its type, infer `body` |
| `If(cond, then, else)` | `cond` must be `Bool`, `then` and `else` must agree |
| `Lambda([p], body)` | Fresh vars for params, infer body, return `Fn([param_tys], body_ty)` |
| `Apply(callee, args)` | Infer callee, unify with `Fn(arg_types, ret)`, return `ret` |
| `do` (macro) | Expands to nested `let [_ e] ...`, return type of last expr |
| `pure` (function) | Wraps value in `IOVal` constructor, returns `IO(a)` |
| `bind` (function) | Unwraps `IOVal`, passes inner value to continuation `a -> IO(b)`, returns `IO(b)` |

### Example: Factorial

```clojure
(defn fact [n]
  (if (= n 0) 1 (* n (fact (- n 1)))))
```

1. Register `fact : Fn([t0], t1)`
2. Infer body with `n : t0`:
   - `(= n 0)` → unify `t0 = Int`, result `Bool` ✓
   - `1` → `Int`
   - `(* n (fact (- n 1)))` → `n : Int`, `(- n 1) : Int`, `fact(Int) : t1`, `* : (Int, Int) -> Int`, so `t1 = Int`
3. Result: `fact : Fn([Int], Int)` = `Int -> Int`

### Trait Method Resolution

After type inference, the typechecker resolves each trait method call to a concrete mangled name. See `docs/traits.md` for full details.

Operators (`+`, `-`, etc.) are registered in the type environment via `deftrait` declarations in the prelude. The `Apply` inference rule handles them uniformly — `(+ 1 2)` is parsed as `Apply(Var("+"), [1, 2])` and the operator is looked up in the environment like any other function.

### Constrained Polymorphism

When a function uses trait methods on type variables that have multiple implementations (e.g., `+` with both Int and Float Num impls), the function becomes constrained polymorphic rather than producing an error. It is monomorphised at call sites. See `docs/constrained-polymorphism.md` for full details.

```clojure
(defn add [x y] (+ x y))
; add :: (fn [:Num a a] a)

(add 1 2)       ; generates add$Int+Int
(add 1.0 2.0)   ; generates add$Float+Float
```

### Higher-Kinded Types

Traits can declare type constructor parameters — type variables of kind `* -> *` rather than `*`. This enables abstractions like Functor:

```clojure
(deftrait (Functor f)
  (fmap [(Fn [a] b) (f a)] (f b)))
```

The type system represents constructor variable applications as `TyConApp(id, args)`. During unification, `TyConApp` collapses to `ADT` when the constructor variable is resolved:

- `TyConApp(f, [Var(a)])` unifies with `ADT("Option", [Int])` → `f ↦ ADT("Option", [])`, `a ↦ Int`
- `apply(subst, TyConApp(f, [Var(b)]))` → `ADT("Option", [apply(subst, Var(b))])`

By codegen time, all `TyConApp` are resolved to concrete `ADT` types. See `docs/hkt.md` for full details.

### Builtins

`print` is pre-registered as `Fn([String], IO(Int))` — takes a String, prints it, returns `IO Int`.

`read-line` is pre-registered as `Fn([], IO(String))` — reads a line from stdin.

`parse-int` is pre-registered as `Fn([String], ADT("Option", [Int]))` — parses a string as an integer, returning `Option Int`. Pure function (no IO wrapper).

`show` is a Display trait method: `forall a. a -> String` — implementations for Int, Bool, String, Float.

### Prelude Types

The prelude defines `Option` as an algebraic data type available to all programs:

```clojure
(deftype (Option a) None (Some [:a val]))
```

`Option` is used by `parse-int` and is available for user code. `None` is a nullary constructor (bare i64 tag 0 at runtime), `Some` is a data constructor (heap `[tag=1, value]`).
