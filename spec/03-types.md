# 3. Type System [Tested]

This section defines the type system of Cranelisp: the set of types, the type inference algorithm, and the rules for type checking programs.

Cranelisp uses Hindley-Milner type inference extended with traits, constrained polymorphism (monomorphisation), and higher-kinded types. All types can be inferred without annotations, but optional type annotations are available to constrain types or add trait requirements (see [Section 2](02-grammar.md) for annotation syntax).

## 3.1 Primitive Types [Tested tests/ring0.rs::float_arithmetic]

Cranelisp has four primitive types. All are immutable and unboxed at runtime.

| Type | Description | Value domain |
|---|---|---|
| `Int` | Signed 64-bit integer | -2^63 to 2^63 - 1 |
| `Bool` | Boolean | `true` or `false` |
| `String` | Immutable UTF-8 string | Arbitrary Unicode text |
| `Float` | IEEE 754 double-precision float | 64-bit floating point |

`Int` values use two's complement representation; arithmetic overflow wraps silently. `Float` values follow IEEE 754 semantics including `NaN`, infinities, and signed zero.

## 3.2 Compound Types [R4 S10]

### 3.2.1 Function Types [Tested tests/repl_experience.rs::defn_with_let_infers_return_type]

```
Fn([T1, T2, ..., Tn], R)
```

A function type describes a callable value taking parameters of types `T1` through `Tn` and returning a value of type `R`. Function types are written in source notation as:

```clojure
(Fn [Int Int] Bool)    ; a function from two Ints to Bool
(Fn [String] (IO Int)) ; a function from String to IO Int
```

All functions are first-class values. At runtime, function values are represented as closures (see [Section 12](12-runtime.md)).

### 3.2.2 Algebraic Data Types [Tested tests/ring1.rs::adt_polymorphic_type]

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

### 3.2.3 IO Type [R4 S10]

```
IO(A)
```

`IO` is a compiler-seeded algebraic data type representing an effectful computation that produces a value of type `A`:

```clojure
(deftype (IO a) (IOVal [:a ioval]))
```

`IO` is defined in the `primitives` module and participates in the type system as an ordinary ADT. Functions that perform side effects (printing, reading input, etc.) MUST return `IO`. Pure functions MUST NOT return `IO`.

Operations such as `pure` and `bind` can be defined as ordinary library functions to compose IO values (see [Section 10](10-io.md) for details).

### 3.2.4 Trace Type [Tested tests/ring4_trace.rs::trace_returns_trace_type_int]

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

`Trace`, `TraceCall`, `trace`, and the field accessor functions (`name`, `params`, `result`, `children`, `nanos`) are defined in the `primitives` module but are NOT auto-imported into user scope. User code must import them explicitly (e.g., `(import [primitives [trace Trace TraceCall]])`) or use qualified names (e.g., `primitives/trace`). A standard library MAY re-export these through a convenience module (e.g., `core.trace`) using the `export` mechanism (see [Section 8.4](08-modules.md#84-export)).

### 3.2.5 TestResult Type [R4]

```
TestResult
```

`TestResult` is a compiler-seeded algebraic data type representing the outcome of running a single test function:

```clojure
(deftype TestResult
  (TestPass [:String name :Int nanos])
  (TestFail [:String name :Int nanos :String reason])
  (TraceFail [:String name :Int nanos :String reason :Trace trace]))
```

| Constructor | Fields | Description |
|---|---|---|
| `TestPass` | `name` (String), `nanos` (Int) | Test returned `None` (pass). `name` is the fully-qualified function name; `nanos` is wall-clock elapsed time. |
| `TestFail` | `name` (String), `nanos` (Int), `reason` (String) | Test returned `Some(reason)` (fail). Produced by `run-test` (no tracing). |
| `TraceFail` | `name` (String), `nanos` (Int), `reason` (String), `trace` (Trace) | Test returned `Some(reason)` (fail) with tracing active. Produced by `trace-test`. `trace` is the full execution trace tree (§3.2.4). |

`TestResult` is a root type — always in scope without import, like `IO` and `Vec`. The separation between `TestFail` and `TraceFail` reflects the two test execution modes: `run-test` runs without instrumentation (fast), while `trace-test` runs with full GOT-swap tracing (slower, diagnostic). Both share `TestPass` for the success case.

A test function is any zero-argument function whose name begins with `test-` and returns `(Option String)`. `None` indicates pass; `Some(reason)` indicates failure with a human-readable reason.

### 3.2.6 Vec Type [Tested tests/ring1.rs::vec_literal_int]

```
Vec(A)
```

`Vec` is a built-in resizable array type parameterized by element type:

```clojure
[1 2 3]          ; Vec Int
["a" "b"]        ; Vec String
```

`Vec` is registered as a built-in type in the `primitives` module. It supports indexed access and functional update operations.

## 3.3 Type Variables [Tested tests/ring1.rs::adt_polymorphic_type]

Type variables are lowercase identifiers that stand for unknown or universally quantified types:

```
a, b, elem, f
```

Type variables are created in two contexts:

1. **During inference**: The typechecker generates fresh type variables (internally numbered as `t0`, `t1`, ...) when the type of an expression is not yet known. These are unified with concrete types as constraints are discovered.

2. **In type schemes**: After generalization, type variables that remain free are universally quantified. In display output, quantified variables are named alphabetically (`a`, `b`, `c`, ...).

Type variables are implicitly universally quantified at function definition boundaries. There is no explicit `forall` syntax in the source language -- quantification is determined by the inference algorithm.

## 3.4 Type Schemes [Tested tests/ring0.rs::let_polymorphism_identity]

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

## 3.5 Type Inference (Algorithm W) [Tested tests/repl_experience.rs::defn_with_let_infers_return_type]

Cranelisp implements Algorithm W, the classic Hindley-Milner type inference algorithm. The typechecker maintains a mutable substitution map that accumulates type equalities as expressions are checked.

### 3.5.1 Core Operations

The inference algorithm relies on five core operations:

**`fresh_var()`** -- Create a new, unique unification variable `Var(id)`. Each call returns a variable with a globally unique integer identifier.

**`unify(A, B)`** -- Assert that types `A` and `B` are equal. This may extend the substitution map with new bindings. Unification fails (producing a type error) if the types are incompatible. See Section 3.8 for the full unification rules.

**`apply(S, T)`** -- Apply substitution `S` to type `T`, recursively replacing any `Var(id)` that has a mapping in `S` with its resolved type. Application is idempotent when the substitution is fully resolved.

**`instantiate(scheme)`** -- Replace a scheme's quantified variables with fresh unification variables, producing a monotype. Constraints from the scheme are propagated to the fresh variables.

**`generalize(T, env)`** -- Quantify over all type variables in `T` that are not free in the environment `env`. Variables with accumulated trait constraints carry those constraints into the resulting scheme.

### 3.5.2 Two-Pass Checking

To support forward references and mutual recursion among top-level definitions, the typechecker uses a two-pass strategy:

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

#### Trace Expression [R4 S20]

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

## 3.6 Constrained Polymorphism [Tested tests/ring2.rs::constrained_add_int]

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

### 3.6.3 Monomorphisation [Tested tests/ring2::constrained_add_int, tests/ring2::constrained_add_float, tests/ring2::constrained_add_both_types]

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

## 3.7 Higher-Kinded Types [R3 S17]

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

## 3.8 Unification Rules [Tested tests/ring1.rs::error_type_mismatch_names_both_types]

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

## 3.9 Type Annotations [Tested tests/ring0.rs::annotated_params]

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
