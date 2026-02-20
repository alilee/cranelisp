# Algebraic Data Types

## Overview

Algebraic data types (ADTs) let users define custom types — product types (structs), sum types (tagged unions), and enums. They are the foundation for data modelling in cranelisp and make the trait system useful for user-defined types.

```clojure
(deftype Point [:Int x :Int y])

(deftype (Option a)
  None
  (Some [:a unwrap]))

(deftype Color Red Green Blue)
```

## Syntax: `deftype`

All `deftype` forms support optional docstrings — a type-level docstring after the name/head, and per-constructor docstrings after the constructor name:

```clojure
(deftype (Option a) "An optional value"
  (None "Represents absence")
  (Some "Wraps a present value" [:a val]))
```

### Product Types

When the body is a bracketed field list, the type name IS the constructor:

```clojure
(deftype Point "A 2D point" [:Int x :Int y])
```

- `Point` is both the type name and the sole constructor
- Fields are alternating `:Type name` pairs in brackets
- `(Point 3 4)` constructs a Point
- Generates accessor functions `x` and `y` (see Field Accessors below)

Polymorphic product type:

```clojure
(deftype (Pair a b) [:a first :b second])
```

### Sum Types

When the body has constructor forms, each constructor is its own variant:

```clojure
(deftype (Option a)
  None
  (Some [:a unwrap]))

(deftype Shape
  (Circle [:Float radius])
  (Rect [:Float width :Float height]))

(deftype Color Red Green Blue)
```

- Nullary constructors: bare `None` or `Red` (no parens needed)
- Data constructors: `(Some [:a unwrap])` — field list in brackets
- Constructors are functions: `Some :: (Fn [a] (Option a))`

### Field Syntax

Inside brackets, fields are alternating `:Type name` pairs:

```clojure
[:Int x :Int y]              ; two Int fields named x and y
[:Float radius]              ; one Float field named radius
[:a first :b second]         ; two polymorphic fields
```

The `:Type name` convention is consistent with constraint syntax `:Num a` — colon always prefixes a type or trait annotating the name that follows.

All fields must have names. No positional (unnamed) fields — every field gets an accessor.

### Shortcut Syntax — Inferred Type Parameters

When field brackets contain bare names (no `:Type` prefix), each unique bare name gets a fresh type variable. Type parameters are inferred and added to the type automatically.

```clojure
;; Shortcut form                        ;; Desugars to
(deftype Option                         (deftype (Option a)
  None                                    None
  (Some [unwrap]))                        (Some [:a unwrap]))

(deftype Result                         (deftype (Result a b)
  (Ok [ok])                               (Ok [:a ok])
  (Err [err]))                            (Err [:b err]))

(deftype Pair [first second])           (deftype (Pair a b) [:a first :b second])
```

**Rules:**

- Bare field name (no `:`) → fresh type variable, assigned letters `a`, `b`, `c`... in order of first appearance across all constructors
- `:Type name` → explicit concrete or polymorphic type, no inference
- Type params on the type name are optional when all field types are inferred
- Mixing concrete and inferred fields within one bracket is allowed:

```clojure
(deftype Named (Named [:String name value]))
;; name is :String (explicit), value gets fresh var 'a'
;; => (deftype (Named a) (Named [:String name :a value]))
```

### Syntax Disambiguation

The parser distinguishes product vs sum by what follows the type name/params:

| Token after type | Form | Description |
|---|---|---|
| `[` | Product type | Single constructor = type name |
| `(` or bare identifier | Sum type | One or more constructor forms |

```clojure
;; Product — bracket body
(deftype Point [:Int x :Int y])
(deftype Pair [first second])               ; shortcut

;; Sum — constructor forms
(deftype (Option a) None (Some [:a unwrap]))
(deftype Option None (Some [unwrap]))        ; shortcut

;; Enum — bare identifiers (nullary-only sum type)
(deftype Color Red Green Blue)
```

### Full Examples

```clojure
;; Product type with named fields
(deftype Point [:Int x :Int y])

;; Polymorphic product type — full form
(deftype (Pair a b) [:a first :b second])

;; Polymorphic product type — shortcut
(deftype Pair [first second])

;; Sum type with named fields — full form
(deftype Shape
  (Circle [:Float radius])
  (Rect [:Float width :Float height]))

;; Sum type — shortcut
(deftype Option None (Some [unwrap]))

;; Sum type — shortcut with multiple type params
(deftype Result (Ok [ok]) (Err [err]))

;; Monomorphic sum type with concrete types
(deftype Bound
  (Max [:Int max])
  (Min [:Int min]))

;; Simple enum
(deftype Color Red Green Blue)
```

## Syntax: `match`

```clojure
(match expr
  [pattern1 body1
   pattern2 body2
   ...])
```

### Patterns

| Pattern | Example | Matches |
|---|---|---|
| Nullary constructor | `None` | The constructor value |
| Constructor + bindings | `(Some x)` | Destructures fields positionally |
| Wildcard | `_` | Anything, binds nothing |
| Variable | `x` | Anything, binds to `x` |

Destructuring is always **positional** — bindings correspond to fields in `deftype` field order.

### Examples

```clojure
;; Sum type matching
(match maybe-val
  [None 0
   (Some x) x])

;; Enum matching
(match color
  [Red "red"
   Green "green"
   Blue "blue"])

;; Product type destructuring
(match point
  [(Point x y) (+ x y)])

;; Wildcard
(match color
  [Red "red"
   _ "other"])
```

### Exhaustiveness

Stage 1 does not check exhaustiveness. A non-exhaustive match that falls through all arms produces a runtime panic.

## Field Accessors

Named fields generate **regular functions** in the enclosing scope. The field name becomes the function name.

```clojure
(deftype Point [:Int x :Int y])

(x (Point 3 4))        ; => 3
(y (Point 3 4))        ; => 4
```

### Product Type Accessors

For product types (single constructor), accessors are total — they always succeed:

```
x :: (Fn [Point] Int)
y :: (Fn [Point] Int)
```

### Sum Type Accessors

For sum type constructors with named fields, accessors are partial — they succeed on the matching variant and panic otherwise:

```
unwrap :: (Fn [(Option a)] a)
radius :: (Fn [Shape] Float)
```

```clojure
(unwrap (Some 42))     ; => 42
(unwrap None)          ; => runtime panic: "unwrap called on None"
```

### Accessors as First-Class Values

Accessor functions are regular functions and work as first-class values:

```clojure
(let [get-x x]
  (get-x (Point 3 4)))   ; => 3
```

### Namespace

Accessor functions are global names. Name clashes will be addressed when modules are added. For now, last definition wins.

## What Constructors Are

- **Nullary constructors** are values: `None :: (Option a)`, `Red :: Color`
- **Data constructors** are functions: `Some :: (Fn [a] (Option a))`, `Point :: (Fn [Int Int] Point)`
- Data constructors participate in auto-currying: `(let [f Some] (f 42))` works
- Nullary constructors in the REPL self-describe: typing `None` shows `None :: (Option a)`
- Constructor names are capitalized by convention

## Type Inference

### Constructor Calls

Data constructors are typed as functions. Calling `(Some 42)` follows the standard `Apply` inference rule:

1. Look up `Some` → instantiate `(Fn [a] (Option a))` with fresh variable
2. Infer argument `42` → `Int`
3. Unify parameter with `Int` → substitution `a = Int`
4. Return type `(Option Int)`

### Match Expressions

The scrutinee and all branch bodies are unified:

1. Infer the scrutinee type
2. For each arm:
   - Unify the pattern's constructor type with the scrutinee type
   - Bind pattern variables to the constructor's field types
   - Infer the body type
3. Unify all body types (all arms must agree)
4. The match expression type is the unified body type

### Polymorphic Types

`(Option a)` is a type constructor parameterized over `a`. Each use site instantiates `a` with a fresh variable. Unification propagates concrete types through.

## Runtime Representation

All values are `i64`. ADT values follow these rules:

### Nullary Constructors

Stored as a bare i64 tag:

```
None = 0
Red = 0, Green = 1, Blue = 2
```

### Data-Carrying Constructors

Stored as a heap pointer to `[tag: i64, field0: i64, field1: i64, ...]`:

```
(Some 42) → heap_ptr → [ 1 | 42 ]
                         tag  field0

(Point 3 4) → heap_ptr → [ 0 | 3 | 4 ]
                           tag  x    y

(Rect 1.0 2.0) → heap_ptr → [ 1 | <f64 bits> | <f64 bits> ]
                               tag   width        height
```

This mirrors the existing closure representation `[code_ptr, cap0, cap1, ...]`.

### Tag Assignment

All constructors of a type get sequential tags starting from 0, in definition order:

| Type | Constructor | Tag |
|---|---|---|
| `Option` | `None` | 0 |
| `Option` | `Some` | 1 |
| `Color` | `Red` | 0 |
| `Color` | `Green` | 1 |
| `Color` | `Blue` | 2 |
| `Shape` | `Circle` | 0 |
| `Shape` | `Rect` | 1 |
| `Point` | `Point` | 0 |

### Match Codegen

Match compiles to a tag-dispatch sequence:

1. Load the tag:
   - For types with only data constructors: `load(scrutinee, offset 0)` — tag is at heap offset 0
   - For types with mixed nullary/data constructors: check if the value IS a small-integer tag (nullary) or a heap pointer (data)
   - For enum-only types: the value IS the tag

2. Branch on the tag using `brif` / jump chain (linear scan for small numbers of variants)

3. For data constructor patterns: load fields from heap at offsets `(i+1) * 8`

4. For wildcard/variable patterns: bind the scrutinee value directly

5. If no arm matches: call a panic function (runtime error)

### Mixed Nullary/Data Tag Discrimination

When a type has both nullary and data constructors (like `Option` with `None` and `Some`), the runtime must distinguish between a small integer tag (nullary) and a heap pointer (data constructor). Strategy:

- Nullary constructors get tags 0, 1, 2, ... (small integers)
- Data constructors store their tag at heap offset 0
- Match codegen: first compare the scrutinee against each nullary tag value; if none match, load the tag from `heap[0]` and dispatch on data constructor tags

### Constructor Codegen

**Nullary constructors**: compile to `iconst.i64 tag`.

**Data constructors**: compile as functions with signature `(params...) -> i64`:

1. `call cranelisp_alloc((1 + num_fields) * 8)`
2. `istore64 tag` at offset 0
3. `istore64 field_i` at offset `(i+1) * 8`
4. Return the heap pointer

### Accessor Codegen

**Product type accessors**: load field from heap at offset `(field_index + 1) * 8`. No tag check needed — only one constructor.

**Sum type accessors**: load tag from `heap[0]`, compare against the expected constructor's tag. If match, load field. If mismatch, call panic.

## REPL Display

ADT values display as their constructor form:

```
cranelisp> (Point 3 4)
(Point 3 4) :: Point

cranelisp> (Some 42)
(Some 42) :: (Option Int)

cranelisp> None
None :: (Option a)

cranelisp> Red
Red :: Color

cranelisp> (Circle 2.5)
(Circle 2.5) :: Shape
```

Nested values display recursively: `(Some (Point 1 2))` → `(Some (Point 1 2))`.

This requires a runtime display path: given a tag and type metadata, format the value by reading fields from heap and recursively displaying inner ADT values.

### REPL Self-Description

Constructors and type names respond usefully when entered bare at the REPL:

```
cranelisp> Point
Point :: (Fn [Int Int] Point)

cranelisp> Some
Some :: (Fn [a] (Option a))

cranelisp> None
None :: (Option a)

cranelisp> Color
Color :: type (Red | Green | Blue)
```

This follows the self-documenting REPL principle — every symbol produces useful feedback.

## Trait Impls for ADTs

### Monomorphic ADT

```clojure
(impl Display Color
  (defn show [c]
    (match c
      [Red "Red"
       Green "Green"
       Blue "Blue"])))
```

### Concrete ADT Instantiation

```clojure
(impl Display (Option Int)
  (defn show [self]
    (match self
      [None "None"
       (Some x) (show x)])))
```

Implements Display for `(Option Int)` specifically. The `(show x)` call in the `Some` arm dispatches to `show$Int`.

### Polymorphic ADT — With Constraints

```clojure
(impl Display (Option :Display a)
  (defn show [self]
    (match self
      [None "None"
       (Some x) (show x)])))
```

`:Display a` in the type target specifies that `a` must implement Display. The impl method becomes a constrained function that is monomorphised at call sites: `(show (Some 42))` generates `show$Option$Int`.

## Scope

### Stage 1 Implements

- `deftype` — product types (bracket body) and sum types (constructor body)
- Named fields `[:Type name ...]` with bare-function accessors
- Shortcut syntax — bare `[name]` infers type parameters
- Type parameters (polymorphic ADTs: Option, Either, Pair)
- Constructors as functions (data constructors) and values (nullary constructors)
- `match` expression with constructor patterns, wildcards, variable binding
- Partial accessor functions for sum type named fields (panic on wrong variant)
- REPL display of ADT values
- `:type` / `:info` for constructors and types
- Trait impls for monomorphic ADTs (`(impl Display Color ...)`)
- Trait impls for concrete ADT instantiations (`(impl Display (Option Int) ...)`)
- Trait impls for polymorphic ADTs with constraints (`(impl Display (Option :Display a) ...)`)

### Stage 1 Does NOT Implement

- Recursive types (`(deftype (List a) Nil (Cons [:a head :(List a) tail]))`)
- Nested patterns in match (`(Some (Point x y))`)
- Exhaustiveness checking
- Literal patterns in match
- Named destructuring in match
- Field update/set syntax

## Limitations

- **No exhaustiveness checking**: non-exhaustive match silently falls through to a runtime panic.
- **Name collisions**: accessor functions are global. Two types with the same field name will shadow each other.
- **Match scrutinee lifetime**: the scrutinee value is not dec'd after the match completes, leaking its reference count. See KNOWN_ISSUES.md.
- **Closure drop glue deferred**: when a closure capturing ADT values is freed, the captured values are not decremented. See KNOWN_ISSUES.md.
