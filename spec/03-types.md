# 3. Type System [Tested]

This section defines the type system of Cranelisp: the set of types, the type inference algorithm, and the rules for type checking programs.

Cranelisp uses Hindley-Milner type inference extended with traits, constrained polymorphism (monomorphisation), and higher-kinded types. All types can be inferred without annotations, but optional type annotations are available to constrain types or add trait requirements (see [Section 2](02-grammar.md) for annotation syntax).

## 3.1 Primitive Types [Tested tests/spec_03_types::primitive_int_display]

Cranelisp has four primitive types. All are immutable and unboxed at runtime.

| Type | Description | Value domain |
|---|---|---|
| `Int` | Signed 64-bit integer | -2^63 to 2^63 - 1 |
| `Bool` | Boolean | `true` or `false` |
| `String` | Immutable UTF-8 string | Arbitrary Unicode text |
| `Float` | IEEE 754 double-precision float | 64-bit floating point |

`Int` values use two's complement representation; arithmetic overflow wraps silently. `Float` values follow IEEE 754 semantics including `NaN`, infinities, and signed zero.

Primitive types follow the same import rules as other names in the `primitives` module (see [§8.9.1](08-modules.md#891-the-primitives-module)). Bare-name references (e.g., `:Int`) MUST come into scope through either prelude re-export or an explicit import (e.g., `(import [primitives [Int Bool Float String]])`); otherwise they are a compile-time "unknown type" error. Fully-qualified references (e.g., `:primitives/Int`) are always available regardless of imports. [S70]

## 3.2 Compound Types [S10]

### 3.2.1 Function Types [Tested crates/cranelisp-typecheck/src/resolve.rs::test_resolve_fn_type]

```
Fn([T1, T2, ..., Tn], R)
```

A function type describes a callable value taking parameters of types `T1` through `Tn` and returning a value of type `R`. Function types are written in source notation as:

```clojure
(Fn [Int Int] Bool)    ; a function from two Ints to Bool
(Fn [String] (IO Int)) ; a function from String to IO Int
```

All functions are first-class values. At runtime, function values are represented as closures (see [Section 12](12-runtime.md)).

### 3.2.2 Algebraic Data Types [Tested crates/cranelisp-typecheck/src/adt.rs::test_resolution_validates_registered_arity]

```
ADT(Name, [A1, A2, ..., An])
```

Algebraic data types are user-defined types declared with `deftype` (see [Section 5](05-definitions.md)). The name is an uppercase identifier; the type arguments are zero or more types.

```clojure
(Option Int)           ; Option applied to Int
(List String)          ; List applied to String
Point                  ; a nullary ADT (no type arguments)
Color                  ; an enum ADT (no type arguments)
```

ADTs may be:
- **Product types** (single constructor with fields): `(deftype Point [:Int x :Int y])`
- **Sum types** (multiple constructors): `(deftype (Option a) None (Some [:a val]))`
- **Enum types** (all constructors nullary): `(deftype Color Red Green Blue)`

### 3.2.3 IO Type [S10]

```
IO(A)
```

`IO` is a compiler-seeded algebraic data type representing an effectful computation that produces a value of type `A`:

```clojure
(deftype (IO a) (IOVal [:a ioval]))
```

`IO` is defined in the `primitives` module and participates in the type system as an ordinary ADT. Functions that perform side effects (printing, reading input, etc.) MUST return `IO`. Pure functions MUST NOT return `IO`.

Operations such as `pure` and `bind` can be defined as ordinary library functions to compose IO values (see [Section 10](10-io.md) for details).

### 3.2.4 Trace Type [Tested crates/cranelisp-typecheck/src/builtins.rs::test_vec_primitives_registered]

```
Trace
```

`Trace` is a compiler-seeded algebraic data type representing a recorded execution call tree:

```clojure
(deftype Trace
  (TraceCall [:String          name
              :(SList String)  params
              :String          result
              :(SList Trace)   children
              :Int             nanos]))
```

`Trace` is defined in the `primitives` module and participates in the type system as an ordinary ADT. It is the result type of the `trace` special form (see [Section 4.12](04-expressions.md#412-trace-expression)). Unlike most ADTs, `Trace` is not parameterized -- it captures runtime information as formatted strings using the canonical value display format (see [Section 12.9](12-runtime.md#129-value-display-format)). The `params` and `children` fields use `SList` (from the `macros` module) for list structure, enabling pattern-matching traversal with `SCons`/`SNil`.

**Form/ADT asymmetry.** There is a deliberate asymmetry between the `trace` *form* and the `Trace` *ADT names*: [S76]

- The **`trace` keyword needs no import**. It is a root special form (see [Section 2.3.10](02-grammar.md#2310-trace----execution-trace) and [Section 4.12.4](04-expressions.md#4124-the-trace-adt)) — always available with no import and no module path, and there is **no** `primitives/trace`. Its name is reserved (see [Section 2.9](02-grammar.md#29-reserved-words)).
- The **`Trace`, `TraceCall`, and field accessor names** (`name`, `params`, `result`, `children`, `nanos`) **DO require import**. They are `primitives`-module entries that are NOT auto-imported into user scope. User code must import them explicitly (e.g., `(import [primitives [Trace TraceCall name params result children nanos]])`) or use qualified names (e.g., `primitives/Trace`).

This mirrors the `Sexp`-in-`macros` precedent (see [Section 9.1](09-macros.md#91-sexp-data-model)): quasiquote works without import because the expander emits qualified `macros/Sexp...` constructors, while bare `Sexp` constructors must be imported. Likewise the `trace` form works without import, while destructuring the returned `Trace` value requires importing the ADT names. A standard library MAY re-export the ADT names through a convenience module (e.g., `core.trace`) using the `export` mechanism (see [Section 8.4](08-modules.md#84-export)).

### 3.2.5 Result Type [S77 — tested-by /qa]

```
Result(A, B)
```

`Result` is a compiler-seeded algebraic data type representing a success-or-failure outcome:

```clojure
(deftype (Result a b)
  (Ok  [:a val])
  (Err [:b err]))
```

| Constructor | Fields | Description |
|---|---|---|
| `Ok`  | `val` (a) | Success carrying a value of type `a`. |
| `Err` | `err` (b) | Failure carrying a value of type `b`. |

`Result` is defined in the `primitives` module and participates in the type system as an ordinary parameterised ADT. It is **not** auto-imported into user scope: user code must import it explicitly (e.g., `(import [primitives [Result Ok Err]])`) or use qualified names (e.g., `primitives/Ok`). It is the return type of the `catch-runtime-error` combinator (see [Appendix A.3](appendix-a-builtins.md#test-discovery-and-error-capture)): `(Ok result)` when a protected thunk completes, `(Err message)` when it raised a runtime error. Both constructors carry data, so both are heap-allocated.

### 3.2.6 Pair Type [Tested tests/spec_03_types::vec_as_function_return_type]

```
Pair(A, B)
```

`Pair` is a compiler-seeded algebraic data type representing a two-field product:

```clojure
(deftype (Pair a b)
  (Pair [:a first :b second]))
```

| Constructor | Fields | Description |
|---|---|---|
| `Pair` | `first` (a), `second` (b) | A value pairing a `first` of type `a` with a `second` of type `b`. |

`Pair` is defined in the `primitives` module and participates in the type system as an ordinary parameterised ADT. It is **not** auto-imported: user code must import it explicitly (e.g., `(import [primitives [Pair]])`) or use qualified names (e.g., `primitives/Pair`). It is the element type of the `discover-tests` result `(Vec (Pair String (Fn [] (Option String))))` (see [Appendix A.3](appendix-a-builtins.md#test-discovery-and-error-capture)) — each pair carries a test's fully-qualified name and its late-bound callable.

A test function is any zero-argument function whose name begins with `test-` and whose type is exactly `(Fn [] (Option String))`. `None` indicates pass; `Some(reason)` indicates failure with a human-readable reason. Test discovery and execution are composed from ordinary library code over `discover-tests` and `catch-runtime-error` (see [Appendix A.3](appendix-a-builtins.md#test-discovery-and-error-capture) and [repl/spec.md §16](../repl/spec.md#16-test-discovery-and-execution)); there is no dedicated test-result type.

### 3.2.7 Vec Type [Tested crates/cranelisp-typecheck/src/resolve.rs::test_resolve_applied_builtin_vec_wrong_arity]

```
Vec(A)
```

`Vec` is a built-in resizable array type parameterized by element type:

```clojure
[1 2 3]          ; Vec Int
["a" "b"]        ; Vec String
```

`Vec` is registered as a built-in type in the `primitives` module. It supports indexed access and functional update operations.

## 3.3 Type Variables [Tested tests/spec_03_types::polymorphic_identity_at_int]

Type variables are lowercase identifiers that stand for unknown or universally quantified types:

```
a, b, elem, f
```

Type variables are created in two contexts:

1. **During inference**: The typechecker generates fresh type variables (internally numbered as `t0`, `t1`, ...) when the type of an expression is not yet known. These are unified with concrete types as constraints are discovered.

2. **In type schemes**: After generalization, type variables that remain free are universally quantified. In display output, quantified variables are named alphabetically (`a`, `b`, `c`, ...).

Type variables are implicitly universally quantified at function definition boundaries. There is no explicit `forall` syntax in the source language -- quantification is determined by the inference algorithm.

This applies equally to a type variable the source author **writes** in a parameter or return **type annotation** and to one the inference engine generates: a lowercase identifier appearing free in an annotation -- whether standing alone (`(defn id [:a x] :a x)`) or nested inside an applied type (`:(Maybe a)`) -- is a type variable in exactly the sense above, and MUST be treated as implicitly universally quantified at the function definition boundary, identically to an inference-generated variable. Such an identifier MUST NOT be treated as a reference to an unknown named type. [S109]

## 3.4 Type Schemes [Tested tests/spec_03_types::let_polymorphism_identity_two_types]

A **type scheme** (or **polytype**) is a type with universally quantified variables and optional trait constraints:

```
forall [v1, v2, ...]. {v1: [T1, T2], v2: [T3]} => T
```

Where:
- `v1, v2, ...` are the quantified type variable identifiers
- The constraint map associates each constrained variable with a list of required trait names
- `T` is the underlying type

A **monomorphic scheme** (or **monotype**) has no quantified variables and no constraints:

```
forall []. {} => Int
```

### 3.4.1 Constraint Syntax in Display

Constrained type schemes are displayed using the `:Trait var` notation in parameter position:

```
add :: (Fn [:Num a :Num a] a)
bar :: (Fn [:Num :Eq a :Num :Eq a] a)
```

Multiple constraints on the same variable are listed consecutively before the variable name.

### 3.4.2 Examples

```
id       :: forall [a]. {} => (Fn [a] a)
const    :: forall [a, b]. {} => (Fn [a b] a)
add      :: forall [a]. {a: [Num]} => (Fn [a a] a)
show     :: forall [a]. {a: [Display]} => (Fn [a] String)
fmap     :: forall [f, a, b]. {f: [Functor]} => (Fn [(Fn [a] b) (f a)] (f b))
```

## 3.5 Type Inference (Algorithm W) [Tested tests/spec_03_types::defn_return_type_inferred_from_body]

Cranelisp implements Algorithm W, the classic Hindley-Milner type inference algorithm. The typechecker maintains a mutable substitution map that accumulates type equalities as expressions are checked.

### 3.5.1 Core Operations

The inference algorithm relies on five core operations:

**`fresh_var()`** -- Create a new, unique unification variable `Var(id)`. Each call returns a variable with a globally unique integer identifier.

**`unify(A, B)`** -- Assert that types `A` and `B` are equal. This may extend the substitution map with new bindings. Unification fails (producing a type error) if the types are incompatible. See Section 3.8 for the full unification rules.

**`apply(S, T)`** -- Apply substitution `S` to type `T`, recursively replacing any `Var(id)` that has a mapping in `S` with its resolved type. Application is idempotent when the substitution is fully resolved.

**`instantiate(scheme)`** -- Replace a scheme's quantified variables with fresh unification variables, producing a monotype. Constraints from the scheme are propagated to the fresh variables.

**`generalize(T, env)`** -- Quantify over all type variables in `T` that are not free in the environment `env`. Variables with accumulated trait constraints carry those constraints into the resulting scheme.

### 3.5.2 Two-Pass Checking

To support forward references and mutual recursion among top-level definitions, the typechecker uses a two-pass strategy. At file scope this applies across all top-level forms; at the REPL it applies across the forms in a single `begin` cluster (see [§5.13.2](05-definitions.md#5132-repl-input-boundary-and-begin-clusters)).

**Pass 1 -- Registration**: All top-level `defn` names are registered with fresh type variables for their parameter types and return type:

```
fact : Fn([t0], t1)    -- parameter and return are unknowns
main : Fn([], t2)
```

**Pass 2 -- Checking**: Each function body is checked in an environment that includes all registered names. Parameter type variables are added to the local environment, the body is inferred, and the result is unified with the function's return type variable. The substitution map accumulates all constraints.

After both passes complete, all function types are generalized into schemes.

This two-pass approach ensures that any function can reference any other function defined in the same scope, regardless of textual order. Recursive and mutually recursive definitions are handled naturally.

### 3.5.3 Inference Rules [Tested]

The following typing judgments define how types are assigned to each expression form. The notation uses:

- `G` for the type environment (mapping names to schemes)
- `S` for the substitution
- `|-` for "entails" (the environment proves the judgment)
- `e : T` for "expression `e` has type `T`"
- `~` for unification

#### Literals

```
-----------
G |- n : Int          (where n is an integer literal)

-----------
G |- x.y : Float      (where x.y is a float literal)

-----------
G |- true : Bool
G |- false : Bool

-----------
G |- "s" : String     (where "s" is a string literal)
```

#### Variable Reference

```
G(x) = forall [a1..an]. C => T
t1..tn = fresh_var()  (one per quantified variable)
T' = T[a1 := t1, ..., an := tn]
constraints from C propagated to t1..tn
--------------------------------------------
G |- x : T'
```

When a variable is referenced, its scheme is looked up in the environment and instantiated with fresh type variables. This is the source of let-polymorphism: each use of a polymorphic name gets independent type variables.

#### Let Binding

```
G |- e1 : T1
G, x : Mono(T1) |- e2 : T2
----------------------------
G |- (let [x e1] e2) : T2
```

The binding value `e1` is inferred, and its type is added to the environment as a monomorphic scheme for the body `e2`. The result type is the type of the body.

Note: In the current implementation, `let` bindings use monomorphic schemes (no generalization at `let`). Generalization occurs only at top-level `defn` boundaries.

#### If Expression

```
G |- c : T_c
unify(T_c, Bool)
G |- e1 : T1
G |- e2 : T2
unify(T1, T2)
----------------------------
G |- (if c e1 e2) : apply(S, T1)
```

The condition MUST unify with `Bool`. Both branches MUST unify with each other. The result type is the (unified) branch type after applying the current substitution.

#### Lambda

```
t1..tn = fresh_var()  (one per parameter)
G, p1:t1, ..., pn:tn |- body : T_body
-------------------------------------------------
G |- (fn [p1 .. pn] body) : Fn([apply(S,t1), ..., apply(S,tn)], apply(S, T_body))
```

Each parameter gets a fresh type variable. The body is inferred in an extended environment. The resulting function type applies the accumulated substitution to both parameter types and return type.

#### Function Application

```
G |- f : T_f
G |- a1 : A1, ..., G |- an : An
t_ret = fresh_var()
unify(T_f, Fn([A1, ..., An], t_ret))
---------------------------------------
G |- (f a1 ... an) : apply(S, t_ret)
```

The callee is inferred, the arguments are inferred left-to-right, and the callee type is unified with a function type constructed from the argument types and a fresh return variable. The result is the return variable after substitution.

If unification fails because the callee accepts more parameters than provided, auto-currying is attempted (see [Section 4](04-expressions.md)).

#### Vec Literal

```
t_elem = fresh_var()
G |- e1 : T1, unify(T1, t_elem)
...
G |- en : Tn, unify(Tn, t_elem)
---------------------------------------
G |- [e1 ... en] : Vec(apply(S, t_elem))
```

All elements MUST have the same type. The result is `Vec` applied to the element type.

#### Match Expression

```
G |- scrut : T_scrut
t_result = fresh_var()
for each arm (pattern_i => body_i):
    bindings_i = check_pattern(pattern_i, T_scrut)
    G, bindings_i |- body_i : T_i
    unify(T_i, t_result)
---------------------------------------
G |- (match scrut [pattern1 body1 ...]) : apply(S, t_result)
```

The scrutinee is inferred, then each arm's pattern is checked against the scrutinee type (producing bindings for pattern variables), and the arm body is inferred in the extended environment. All arm bodies MUST unify with a single result type.

Pattern checking rules:
- **Constructor pattern** `(Ctor x y ...)`: The constructor's type MUST unify with the scrutinee type. Each binding variable gets the type of the corresponding field.
- **Variable pattern** `x`: Binds `x` to the scrutinee type.
- **Wildcard pattern** `_`: Matches anything, introduces no bindings.

#### Trace Expression [S20]

```
G |- expr : T
---------------------------------------
G |- (trace expr) : Trace
```

The body expression `expr` is inferred normally. The result type of `(trace expr)` is always `Trace`, regardless of the type of `expr`. The type `T` is not preserved in the result type — trace captures runtime information as formatted strings. See [Section 4.12](04-expressions.md#412-trace-expression) for the full evaluation semantics.

### 3.5.4 Worked Example

Consider the factorial function:

```clojure
(defn fact [n]
  (if (= n 0) 1 (* n (fact (- n 1)))))
```

**Pass 1**: Register `fact : Fn([t0], t1)`.

**Pass 2**: Infer body with `n : t0`:

1. `(= n 0)`:
   - `=` is an `Eq` trait method: `(Fn [a a] Bool)` with fresh `a = t2`
   - `n : t0`, unify `t0 ~ t2`
   - `0 : Int`, unify `t2 ~ Int`, therefore `t0 ~ Int`
   - Result: `Bool`

2. `(if (= n 0) 1 (* n (fact (- n 1))))`:
   - Condition `Bool` -- matches
   - Then branch: `1 : Int`
   - Else branch: `(* n (fact (- n 1)))`
     - `(- n 1)`: `n : Int`, `1 : Int`, result `Int`
     - `(fact (- n 1))`: `fact : Fn([Int], t1)`, arg `Int`, result `t1`
     - `(* n ...)`: `* : Fn([Int, Int], Int)`, so `t1 ~ Int`
   - Unify branches: `Int ~ Int`

3. Result after substitution: `fact :: (Fn [Int] Int)`

## 3.6 Constrained Polymorphism [Tested tests/spec_03_types::constrained_add_int]

When a function uses trait methods on type variables and multiple trait implementations exist (e.g., `+` is implemented for both `Num Int` and `Num Float`), the function becomes **constrained polymorphic**. Rather than producing an ambiguity error, the typechecker records the constraints and defers compilation.

### 3.6.1 Constraint Detection

During inference, when a trait method is called on an unresolved type variable and multiple implementations exist for that trait, the type variable acquires a trait constraint:

```clojure
(defn add [x y] (+ x y))
```

Here `+` is a `Num` trait method. The parameter types remain as type variables, but gain the constraint `Num`. The resulting scheme is:

```
add :: forall [a]. {a: [Num]} => Fn([a, a], a)
```

Constraints can also be explicitly annotated on parameters:

```clojure
(defn add [:Num x :Num y] (+ x y))
```

Both forms produce the same constrained scheme.

### 3.6.2 Constraint Propagation

Constraints propagate through three mechanisms:

- **Unification**: When two type variables are unified, their constraint sets are merged.
- **Instantiation**: When a constrained scheme is instantiated, constraints are copied to the fresh type variables.
- **Generalization**: Constraints on variables that are being quantified are preserved in the resulting scheme.

### 3.6.3 Monomorphisation [Tested tests/spec_03_types::constrained_add_int, tests/spec_03_types::constrained_add_float, tests/spec_07_traits::constrained_polymorphism_int_then_float]

Constrained functions are compiled by **monomorphisation** at call sites. Each distinct combination of concrete type arguments generates a specialized version of the function:

```clojure
(add 1 2)       ; generates add$Int+Int   : Fn([Int, Int], Int)
(add 1.0 2.0)   ; generates add$Float+Float : Fn([Float, Float], Float)
```

The monomorphisation process:

1. At a call site, the concrete argument types are determined by inference.
2. The constrained scheme's type variables are mapped to the concrete types.
3. Deferred trait method resolutions are re-resolved with the concrete types.
4. A specialized function definition is emitted with a mangled name.
5. The call site is rewritten to dispatch to the specialized version.

### 3.6.4 Name Mangling

Specialization names are formed by appending the concrete parameter types, separated by `+`:

```
function_name$Type1+Type2+...+TypeN
```

Examples:
- `add$Int+Int`
- `add$Float+Float`
- `compare$String+String`

### 3.6.5 Iterative Monomorphisation

If a constrained function calls another constrained function, the inner call generates additional monomorphisation requests. The typechecker processes these iteratively until no new requests remain, ensuring that transitive specialization chains are fully resolved.

### 3.6.6 Restrictions

- **No first-class constrained values**: A constrained function cannot be used as a value (e.g., passed to a higher-order function) because the concrete types are not known. The expression `(let [f add] ...)` where `add` is constrained produces a type error. The function MUST be called with arguments so that the concrete types can be determined.

- **No constrained closures**: Closures that capture constrained functions are not supported.

## 3.7 Higher-Kinded Types [Tested+Neg tests/spec_07_traits::hkt_deftrait_declaration_with_type_constructor_parameter_succeeds, tests/spec_07_traits::hkt_impl_on_primitive_type_is_rejected_neg]

Cranelisp supports **type constructor parameters** in trait declarations. This enables abstractions over type constructors -- types that take type arguments to produce concrete types (e.g., `Option`, `List`).

### 3.7.1 Type Constructor Variables

In a trait declaration, a lowercase parameter may range over type constructors (kind `* -> *`) rather than concrete types (kind `*`):

```clojure
(deftrait (Functor f)
  (fmap [(Fn [a] b) (f a)] (f b)))
```

Here `f` is a **constructor variable**. The expressions `(f a)` and `(f b)` represent the application of `f` to type arguments `a` and `b` respectively.

### 3.7.2 Type Constructor Application

The type system represents constructor variable applications as `TyConApp`:

```
TyConApp(f_id, [A1, ..., An])
```

This represents the type expression `(f A1 ... An)` -- the constructor variable `f` applied to type arguments. `TyConApp` is an intermediate form that exists only during type checking. By code generation time, all `TyConApp` nodes MUST be resolved to concrete `ADT` types through substitution. There is zero runtime cost.

### 3.7.3 TyConApp Unification

When a `TyConApp` unifies with a concrete `ADT`, the constructor variable binds to the unapplied type constructor:

```
TyConApp(f, [Var(a)])  ~  ADT("Option", [Int])
  => f  |-> ADT("Option", [])     (the constructor itself)
  => a  |-> Int
```

After substitution, any other occurrence `TyConApp(f, [Var(b)])` becomes `ADT("Option", [apply(S, Var(b))])` -- the constructor applied to whatever `b` resolves to.

When two `TyConApp` nodes unify:

```
TyConApp(f1, [A1, ..., An])  ~  TyConApp(f2, [B1, ..., Bn])
  => f1 |-> Var(f2)    (if f1 != f2)
  => unify(A1, B1), ..., unify(An, Bn)
```

### 3.7.4 Implementing HKT Traits

Implementations supply a bare type constructor name as the target:

```clojure
(impl Functor Option
  (defn fmap [f opt]
    (match opt
      [None None
       (Some x) (Some (f x))])))
```

The target `Option` (not `(Option a)`) is matched against the constructor variable `f`. The typechecker validates that the target's arity matches the expected constructor arity -- `Option` takes 1 type parameter, matching the usage `(f a)` in the trait declaration.

Primitive types (`Int`, `Bool`, `String`, `Float`) are rejected as HKT impl targets because they are not type constructors.

### 3.7.5 Kind Checking

Kind checking is **implicit**. There is no explicit kind annotation syntax (e.g., `* -> *`). Instead, the arity of a constructor variable is determined by its usage in method signatures: if `f` appears as `(f a)`, it has arity 1; if as `(f a b)`, arity 2. Validation occurs at impl registration time when the target type's parameter count is checked against the expected arity.

### 3.7.6 Dispatch

HKT trait methods dispatch through the standard trait resolution mechanism (see [Section 7](07-traits.md)). The dispatch parameter is determined by scanning the method's parameter types for the first one containing a constructor application. For `fmap`, the second parameter `(f a)` carries the constructor, so dispatch uses the second argument.

HKT methods are **not** constrained polymorphic functions. Although the scheme carries constraints on constructor variables, the trait dispatch mechanism -- not monomorphisation -- resolves the concrete implementation. At every call site, the concrete type constructor is known.

### 3.7.7 Examples

```clojure
(fmap inc (Some 5))               ; => (Some 6)    -- dispatches to fmap$Option
(fmap inc (list 1 2 3))           ; => (list 2 3 4) -- dispatches to fmap$List
(fmap inc None)                   ; => None         -- dispatches to fmap$Option
(fmap (fn [x] (* x 2)) (Some 3)) ; => (Some 6)
```

## 3.8 Unification Rules [Tested tests/spec_03_types::unification_int_vs_string_errors]

Unification asserts that two types are equal, extending the substitution map as needed. The following table defines all unification cases. Both input types have the current substitution applied before matching.

### 3.8.1 Trivial Cases

| Left | Right | Result |
|---|---|---|
| `Int` | `Int` | Success |
| `Bool` | `Bool` | Success |
| `String` | `String` | Success |
| `Float` | `Float` | Success |

Primitive types unify only with themselves.

### 3.8.2 Variable Binding

```
unify(Var(id), T):
    if T = Var(id):  success (same variable)
    if occurs(id, T):  ERROR "infinite type"
    else:  record id |-> T in substitution
```

When unifying two distinct type variables `Var(id1)` and `Var(id2)`, the constraints of both variables are merged onto the surviving variable.

The **occurs check** prevents construction of infinite types. If variable `id` appears anywhere within type `T` (other than as `T` itself), unification fails. For example, unifying `t0` with `Fn([t0], Int)` would create the infinite type `Fn([Fn([Fn([...], Int)], Int)], Int)`.

### 3.8.3 Function Types

```
unify(Fn([P1..Pn], R1), Fn([Q1..Qm], R2)):
    if n != m:  ERROR "arity mismatch"
    for i in 1..n:  unify(Pi, Qi)
    unify(R1, R2)
```

Function types unify when they have the same number of parameters. Parameters are unified pairwise, then return types are unified.

### 3.8.4 Algebraic Data Types

```
unify(ADT(name1, [A1..An]), ADT(name2, [B1..Bm])):
    if name1 != name2:  ERROR "type mismatch"
    if n != m:  ERROR "type argument count mismatch"
    for i in 1..n:  unify(Ai, Bi)
```

ADTs unify when they have the same name. Type arguments are unified pairwise.

**Type identity is nominal and fully-qualified.** The `name` compared above is the ADT's fully-qualified identity — its home module together with its type name (`FQTypeName`), not the bare name. Two ADTs declared in **different modules** are therefore **distinct types even when they share a bare name and have byte-identical definitions**: `primitives/Option` and `fn.option/Option` do NOT unify, and a value of one does not match a constructor pattern of the other (`primitives/None` does not match `fn.option/Option`'s `None`). This is the standard nominal-typing property; structural coincidence never causes two independently-declared types to be interchangeable. It is the type-system backdrop for the fully-qualified name-resolution discipline in [§8.6.4](08-modules.md#864-conflict-rules): because same-named types from different modules are genuinely different, the fully-qualified reference (`module/Name`) is the unambiguous way to name exactly the one intended.

### 3.8.5 Type Constructor Application

```
unify(TyConApp(f, [A1..An]), ADT(name, [B1..Bm])):
    if n != m:  ERROR "arity mismatch"
    record f |-> ADT(name, []) in substitution
    for i in 1..n:  unify(Ai, Bi)

unify(TyConApp(f1, [A1..An]), TyConApp(f2, [B1..Bm])):
    if n != m:  ERROR "arity mismatch"
    if f1 != f2:  record f1 |-> Var(f2) in substitution
    for i in 1..n:  unify(Ai, Bi)
```

When a `TyConApp` meets a concrete `ADT`, the constructor variable is bound to the bare type constructor (the ADT name with empty type arguments). When two `TyConApp` nodes meet, one constructor variable is bound to the other.

### 3.8.6 Incompatible Types

All other combinations produce a type error:

```
unify(Int, Bool):       ERROR "type mismatch: Int vs Bool"
unify(Fn(..), ADT(..)): ERROR "type mismatch"
unify(Int, Fn(..)):     ERROR "type mismatch"
```

Unification is symmetric: `unify(A, B)` and `unify(B, A)` produce the same result.

## 3.9 Type Annotations [Tested tests/spec_03_types::annotated_params_int]

The annotation form is **`:Type form`** — the `:Type` (or `:(Applied Type)`) introducer is a reader-macro-style prefix that **binds the immediately-following form**, in **all** positions, and is never a standalone atom or variable reference (e.g. `:(Option Int) None`, `:(Vec Int) []`). It is **not** written `(: Type form)`: a parenthesised bare-colon (or leading-`:Type`) list is an ordinary application, not an annotation. This is the syntax used both to annotate a value expression (see [§4.9](04-expressions.md#49-type-annotation)) and to pin an otherwise-ambiguous polymorphic form to a concrete type (see [§3.11](#311-ambiguous-types)). The remainder of this section covers annotations in parameter position.

Type annotations constrain the inferred type of a parameter. They appear as colon-prefixed symbols before parameter names in `defn` and `fn` forms:

```clojure
(defn add [:Int x :Int y] (+ x y))   ; concrete type annotations
(defn show-it [:Display x] (show x)) ; trait constraint annotation
```

### 3.9.1 Concrete Annotations

A concrete type annotation (`:Int`, `:Bool`, `:String`, `:Float`, or a user-defined type name) unifies the parameter's type variable with the named type. This constrains inference and can catch type errors earlier.

### 3.9.2 Trait Constraint Annotations

A trait name annotation (`:Num`, `:Display`, `:Eq`, `:Ord`, etc.) adds a trait constraint to the parameter's type variable without fixing it to a concrete type. The parameter remains polymorphic but is restricted to types that implement the named trait.

Multiple annotations can be stacked on a single parameter:

```clojure
(defn foo [:Num :Display x] ...)  ; x must implement both Num and Display
```

### 3.9.3 Annotation Resolution

When the annotation name is ambiguous (could be either a type or a trait), the typechecker first attempts to resolve it as a concrete type. If no type with that name exists, it is resolved as a trait constraint. If neither exists, a type error is produced.

## 3.10 Rank-1 Hindley-Milner [Tested tests/regression::mono_tier2_fold_accumulator_not_over_monomorphised]

Cranelisp is a **rank-1** (prenex, predicative) Hindley-Milner language. Universal quantification appears only at the outermost level of a type scheme (see [§3.4](#34-type-schemes)) — never nested inside a function parameter, an ADT field, or any other position within a type. This is a normative property of the type system, and the following requirements MUST hold:

- **No quantified types in value position.** A value never has a polytype. Every value, binding, parameter, and field carries a **monotype** at the point it is used. Type schemes exist only as the generalized signatures of top-level definitions (and other generalization boundaries per [§3.5](#35-type-inference-algorithm-w)); they are not first-class and cannot be stored, passed, or returned. There is no rank-2 (or higher) polymorphism: a function MUST NOT take a polymorphic function as an argument and use it at two different types within its body. [S84]

- **Instantiation at every use site.** Each reference to a polymorphic name instantiates its scheme with fresh unification variables (see the Variable Reference rule in [§3.5.3](#353-inference-rules)). Distinct uses of the same polymorphic name receive independent instantiations; this is the sole source of polymorphism in the language. [S84]

- **Monomorphic recursion.** A recursive (or mutually recursive) call MUST use the *same* monotype instantiation of the recursive definition that is in force while its body is being checked — it MUST NOT instantiate the definition polymorphically at the recursive call. Polymorphic recursion (a recursive call at a type strictly more general than, or otherwise differing from, the enclosing definition's checked instantiation) is **not supported** and MUST be rejected as a type error. This is the standard Hindley-Milner restriction and is what keeps full monomorphisation-from-roots (see [§3.6.3](#363-monomorphisation)) finite and complete. [S84]

**Constrained-polymorphism corollary.** The restrictions in [§3.6.6](#366-restrictions) — no first-class constrained values, no constrained closures — are a direct consequence of rank-1: because a constrained function has no concrete monotype until its type variables are pinned at a call site, it cannot occupy value position (where a monotype is required). Rank-1 is the broader guarantee; [§3.6.6](#366-restrictions) is its constrained-polymorphism instance. [S84]

**Why this matters (informative).** Rank-1 + monomorphic recursion is the precondition under which **every reachable function instance has fully concrete parameter and result types** once the program is monomorphised from its roots. The set of `(definition, concrete-type-arguments)` instances reachable from the program entry points is finite, and each is compiled to a concrete specialization. This is why representation can be a backend-internal detail (see [§12.1](12-runtime.md#121-value-representation)) and why no unresolved type variable ever needs a runtime representation — a property the ambiguity rule in [§3.11](#311-ambiguous-types) makes total by rejecting any *codegen-reaching* use that retains a free variable (a named polymorphic definition stays sound and code-less until a concrete use pins it; a bare polymorphic value at the REPL is displayed by introspection — see [§3.11.4](#3114-the-three-dispositions-are-exhaustive-and-consistent)).

## 3.11 Ambiguous Types [S84]

Cranelisp has **no defaulting rule.** There is no Haskell-style numeric defaulting and no implicit selection of a concrete type for an otherwise-unconstrained type variable. An unconstrained type variable is never silently resolved to `Int`, `()`, or any other type.

### 3.11.1 The ambiguity rule is scoped to codegen-reaching value positions [Tested tests/regression::mono_ambiguous_unconstrained_top_level_var_rejected_neg]

**Typecheck produces only concrete types.** A residual type variable remaining in a **codegen-reaching value form** after inference is a **type error** (ambiguous). The source MUST disambiguate it with a `:Type form` annotation (see [§3.9](#39-type-annotations) and [§4.9](04-expressions.md#49-type-annotation)) for the program to compile. A free type variable is **ambiguous** exactly when a value carrying it must be turned into a runtime value — i.e., when it **reaches code generation** — and no reachable use site pins it to a concrete type. Ambiguity is a property of a *use that forces codegen*, not a property of a type or a definition in isolation.

**The strictness is full concreteness — no type variable — NOT machine-shape determinacy.** There is **no representation-based exemption.** Cranelisp does **not** admit an unpinned form merely because its runtime representation would be the same whatever the type variable resolves to (e.g. "always a heap pointer", "always a closure"). A form whose finalized type retains a free type variable in a codegen-reaching value position is rejected even when its machine shape is determinate. The following are **all type errors** when their type variable is unpinned in a codegen-reaching position:

- `(Vec a)` — e.g. the empty vec-literal `[]` (see [§4.10](04-expressions.md#410-vec-literal)) used at an unresolved element type;
- `(Fn [a] a)` — a polymorphic function value at an unresolved type;
- `(Option a)` — e.g. the bare nullary constructor `None` used at an unresolved payload type;
- any other type retaining a free variable that reaches codegen.

**Ambiguity is a type error.** If a polymorphic value with a free type variable must be **monomorphised for code generation** — because it occupies a value position that is actually evaluated to a runtime value (e.g., a value bound by `let` and consumed at runtime, an argument passed to a function that is itself evaluated, the operand of an arithmetic or constructor application that produces a runtime result) — and **no reachable use site pins the variable to a concrete type**, the program MUST be rejected with a type error. There is no concrete instance to compile (no machine representation is the point — even a determinate one does not rescue an unpinned variable), and Cranelisp does not default; therefore the form is rejected rather than admitted. [S84]

The diagnostic intent is to report this as an **ambiguous type** at the site of the unresolved variable and to direct the user to add a type annotation (see [§3.9](#39-type-annotations) and [§4.9](04-expressions.md#49-type-annotation)) that pins the variable. Worked examples:

- `(is-some None)` — `None` has type `(Option a)`; if `a` is not pinned by any reachable use and the application reaches codegen, this is **ambiguous → error**. Fix by annotating the constructor concrete: `(is-some :(Option Int) None)`.
- `(id [])` — `[]` has type `(Vec a)`; if the element type `a` is unpinned and the application reaches codegen, this is **ambiguous → error**. Fix by annotating the literal concrete: `(id :(Vec Int) [])`.
- `(identity None)` evaluated as a runtime value, whose result type is `(Option a)` with `a` unconstrained and reaching codegen with no pinning use site, is ambiguous; annotating it `:(Option Int) (identity None)` (or pinning `None` itself, `(identity :(Option Int) None)`) resolves the ambiguity (see [§4.9.2](04-expressions.md#492-applied-type-annotations)).
- `(Ok 42)` constructed as a runtime value has type `(Result Int b)`: the `Int` is determined by the payload `42`, but the `Err`-arm payload variable `b` is a **phantom** — it appears in the value's type but no `b`-typed runtime value is ever materialised by the `Ok` constructor. **A phantom variable is NOT exempt.** Any free type variable in a codegen-reaching value position — whether it *occurs in* a materialised payload or is a phantom type-argument with no runtime witness — is ambiguous, because no concrete instance can be chosen and Cranelisp does not default. `(Ok 42)` reaching codegen with `b` unpinned is therefore **ambiguous → error**; fix by annotating the construction concrete: `:(Result Int String) (Ok 42)`. Symmetrically `(Err "oops")` is `(Result a String)` with phantom `a`, pinned by `:(Result Int String) (Err "oops")`. (The rule is full concreteness — *no free variable* — not "every variable that names a materialised value"; phantom and occurring variables are treated identically.) [S84]

In each case the annotation is the `:Type form` form — the `:Type` reader-macro-style introducer binding the immediately-following form (see [§4.9](04-expressions.md#49-type-annotation)). It is **not** written `(: Type form)` (a parenthesised bare-colon list is an application, not the annotation — see [§4.9](04-expressions.md#49-type-annotation) and [§2.3.8](02-grammar.md#238-type-annotation)).

#### 3.11.1.1 Why import-site restriction cannot resolve this (rationale) [S84]

Restricting *import* ambiguity does **not** avoid the use-site ambiguity rule, and so cannot replace it. An imported polymorphic type — e.g. `Option` imported as `(Option a)` with **no concrete type specified** at the import — can legitimately be used at **two different concrete types within a single module** (`(Option Int)` in one expression, `(Option String)` in another). There is therefore no single concrete type the import could be pinned to: pinning at the import would be wrong for at least one use. The ambiguity is intrinsically a property of each **use site**, not of the import. The only sound resolution is to require the **source to annotate the ambiguous form** at the use site that reaches codegen without pinning. This is why §3.11.1 is a use-site/codegen rule, and why no amount of import-level discipline removes the need for it.

### 3.11.2 A bare polymorphic value at the REPL is NOT ambiguous [S84]

Entering a **bare, unpinned polymorphic value** at the REPL — `None` (type `∀a. (Option a)`), `[]` (type `∀a. (Vec a)`), or any other value whose finalized type retains an unconstrained, legitimately-quantified scheme variable — is **NOT an error.** Such an input does not reach code generation as a runtime value: there is no slot to fill, no specialization to emit, and no machine representation to choose. Instead, the REPL **displays the value's polymorphic type via introspection**, in `:Type value` form (e.g. `:(…/Option a) Option.None`, or the `Vec` type prefix with `[]`). This is the self-documenting-REPL principle: every valid language construct entered at the REPL produces useful feedback — here, the form's polymorphic type — rather than an opaque rejection. The normative display contract for this case is owned by `repl/spec.md` (the REPL experience specification); §3.11 only fixes that this case is a **type-display disposition, not an ambiguity error**. [S84]

This does not weaken the no-defaulting rule: the REPL does **not** pick a concrete type for the displayed value. It reports the value's polymorphic type as-is. The §3.11.1 ambiguity error still fires the moment that same value is placed in a position that forces codegen without pinning the variable (e.g. `(let [x None] (some-runtime-use x))` where `x` must become a runtime value at an unpinned type).

### 3.11.3 A named polymorphic definition with result-only free variables is SOUND, not ambiguous [Tested tests/regression::mono_ambiguous_neg_does_not_reach_codegen]

A **named top-level definition** whose generalized scheme retains free type variables that appear **only in its result** — `(defn empty [] [])` of type `∀a. (Fn [] (Vec a))`, `(defn ambig [] None)` of type `∀a. (Fn [] (Option a))`, or any `pure`/`empty`-style nullary constructor wrapper — is **admitted, not rejected.** Under rank-1 HM (see [§3.10](#310-rank-1-hindley-milner)), such a definition is a legitimate polymorphic scheme: it is **dead for code generation until instantiated at a concrete use site**, where instantiation-at-use (§3.10) pins the variable and monomorphisation mints a concrete instance for that use. The definition itself emits no specialization; only its concrete uses do. [S84]

The ambiguity error of §3.11.1 is therefore about a **use that forces code generation without pinning the variable** — never about the *definition*. A named polymorphic definition that is never concretely used is sound and simply contributes no code; a named polymorphic definition that *is* concretely used is monomorphised at each pinning use site. Rejecting such definitions would also reject every `empty`/`pure`-style library function, which is not the intent: there is no carve-out needed because there is no rule to carve out — a definition is not a codegen-reaching value position.

**Definitions are mono sources with polymorphic schemes — not ambiguous.** The ambiguity error is a **use-site / codegen property only**. The following are **definitions**, each a single mono source carrying a polymorphic scheme, and **none is ambiguous**:

- A **polymorphic constructor definition** — e.g. `None` declared by `(deftype (Option a) None (Some [:a v]))`. There is **exactly one `None`** (a single polymorphic constructor of scheme `∀a. (Option a)`); there is no definition-site ambiguity because there is nothing to choose between — `None` is one constructor, used at whatever concrete `a` each use site pins. Likewise `Some`, and every other constructor.
- A **generic `defn`** — e.g. `(defn id [x] x)` of scheme `∀a. (Fn [a] a)`. The definition is one function; its uses are monomorphised at the concrete types they pin.
- The **vec-literal special form** itself (`[...]`, see [§4.10](04-expressions.md#410-vec-literal)) — a variadic special form whose zero-element case `[]` has scheme `(Vec a)`. The form is one mono source; an individual unpinned `[]` is ambiguous only at a codegen-reaching *use*, never as "the form."

Ambiguity arises only when a **use** of one of these reaches code generation with its instantiated type variable left unpinned (disposition 2, §3.11.4). The same `None` may be used at `(Option Int)` in one place and `(Option String)` in another; each such use is pinned independently — which is exactly why import-site restriction cannot resolve the ambiguity (see [§3.11.1.1](#31111-why-import-site-restriction-cannot-resolve-this-rationale)) and the *source must annotate* the unpinned use.

### 3.11.4 The three dispositions are exhaustive and consistent [S84]

A polymorphic form whose finalized type retains a free type variable falls into exactly one of three dispositions, and these are exhaustive:

1. **Named definition (or any non-concrete definition with result-only free variables) → admitted, code-less until use.** The definition is a legitimate scheme; it produces no specialization on its own and is monomorphised at each concrete use site. (At the implementation level, such a definition is *slot-less* in the symbol table — it carries no code-generation slot until a concrete use mints one; see [§3.6.3](#363-monomorphisation) and [§12.1](12-runtime.md#121-value-representation).)

2. **A use in a codegen-reaching value position with the variable unpinned → ambiguity type error (§3.11.1).** A runtime value must be produced at an unresolved type, no use site pins it, and Cranelisp does not default; the program is rejected with an "ambiguous type; add an annotation" error.

3. **A bare polymorphic value displayed at the REPL → type-display via introspection (§3.11.2), not an error.** No runtime value is produced; the REPL reports the value's polymorphic type.

These three are consistent: each rests on the same principle — *a type variable never reaches code generation*. A non-concrete definition reaches it only after a concrete use pins it (disposition 1); a codegen-forcing use with no pinning use site is rejected before it can (disposition 2); a REPL bare display never reaches codegen at all (disposition 3). No defaulting occurs in any of the three.

**Rationale (informative).** Under full monomorphisation-from-roots (see [§3.6.3](#363-monomorphisation) and [§3.10](#310-rank-1-hindley-milner)), there is no concrete instance to compile for a form whose type retains an unconstrained variable — there is nothing to specialize it to, and no machine representation to choose. Rejecting *codegen-reaching* ambiguous uses (rather than defaulting) keeps value representation a backend-internal detail and makes the invariant "no unresolved type variable reaches code generation" **total**: legitimately-quantified scheme variables are eliminated by instantiation-at-use (§3.10); a residual free variable in a codegen-reaching position is caught as a type error (disposition 2) rather than reaching the backend; and a bare polymorphic value at the REPL is displayed by introspection (disposition 3) rather than forced through codegen. The invariant is preserved *because* the ambiguity check is scoped to the positions that would otherwise violate it — not by rejecting every polymorphic form.

> **Enforcement seam (informative — for implementers).** This is a *rule*; the *check* that realizes it is a typechecker responsibility, performed at the **post-inference generalization/finalization boundary**, before code generation. The check fires for a form that must be monomorphised for codegen (disposition 2) whose finalized type still contains a free unification variable that no reachable instantiation pins; it MUST raise a type error ("ambiguous type; add an annotation"). It MUST NOT fire for a named polymorphic definition with result-only free variables (disposition 1 — sound, dead-for-codegen until instantiated) nor for a bare polymorphic value entered at the REPL for display (disposition 3 — reported via introspection). At the implementation level the structural slot model realizes dispositions 1 and 3: a non-concrete definition is slot-less (it carries no code-generation slot, and is monomorphised at concrete use sites that mint concrete instances), and a bare-value REPL input is read by introspection rather than compiled; the ambiguity check is the typechecker-side complement to the backend's "no type variable reaches codegen" structural property, together making a residual type variable at code generation impossible by construction. The typechecker's `contains_var`-style residual-variable detector, applied at codegen-reaching value positions, is the natural site for this check.
