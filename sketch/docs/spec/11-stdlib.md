# 11. Standard Library (Non-Normative)

> **This section is non-normative.** The Cranelisp language does not mandate a specific standard library. This section documents the reference implementation's choices -- the types, traits, functions, and macros it provides. Other implementations may provide different standard libraries, provided they conform to the language-level requirements in Sections 1-10 and 12.

This section describes the standard library of the reference implementation: the compiler-seeded types and functions, the core library modules, the prelude, and the implicit prelude import mechanism. The standard library provides the types, traits, functions, and macros that make the core language practical without being required for it to function.

## 11.1 Module Organization

The standard library is organized into three layers: compiler-seeded synthetic modules, core library modules, and the prelude re-export layer.

```
primitives (synthetic)     -- builtin types, functions, IO ADT
macros (synthetic)         -- Sexp, SList ADTs for macro system
core                       -- re-export shell
  core.numerics            -- Num, Eq, Ord traits and implementations
  core.formats             -- Display trait and implementations
  core.collections         -- Functor trait, List type and operations
  core.option              -- Option type and Functor impl
  core.sequences           -- Seq type, lazy operations, unified API
  core.io                  -- pure, bind (IO monadic operations)
  core.syntax              -- prelude macros, SList helpers
prelude                    -- re-exports from core.* and select primitives
```

### 11.1.1 Synthetic Modules

The `primitives` and `macros` modules are **synthetic** -- they are populated by the compiler during initialization, not loaded from source files. They contain types and functions that cannot be expressed in user code because they require host-language implementations or special compiler support.

### 11.1.2 Core Library

The `core` module is a source-level module (`lib/core.cl`) that declares submodules and re-exports their public names:

```clojure
(mod numerics)
(mod formats)
(mod collections)
(mod option)
(mod sequences)
(mod io)
(mod syntax)
(mod derive)

(export [numerics [*]
        formats [*]
        collections [*]
        option [*]
        sequences [Seq range-from iterate repeat to-list seq map filter take drop reduce]
        io [*]
        syntax [const const- def def- list do cond str -> ->> case bind! vec]
        derive [derive derive-Eq derive-Ord derive-Display]])
```

The `syntax`, `sequences`, and `derive` modules use explicit export lists to prevent internal helpers from polluting the prelude namespace. Only user-facing macros are re-exported from `syntax` (`sconcat`, `slist`, `sfold`, `sreverse`, `sempty?` are internal). The `sequences` module exports only the public API (`Seq`, `range-from`, `iterate`, `repeat`, `to-list`, `seq`, `map`, `filter`, `take`, `drop`, `reduce`), hiding lazy-sequence internals (`lazy-filter`, `lazy-take`, `lazy-drop`, `lazy-reduce`, `list-to-seq`, `vec-to-seq`, `SeqCons`, `SeqNil`). Only the four `derive` macros are re-exported from `derive`; all helper functions are private (`defn-`). The quasiquote `~@` operator uses `sconcat` via qualified reference (`core.syntax/sconcat`).

Each submodule imports `(primitives [*])` to access compiler-seeded types and functions. Submodules MAY also import from sibling submodules when they depend on types or traits defined there.

### 11.1.3 Prelude

The `prelude` module (`lib/prelude.cl`) re-exports the entire core library plus select primitives that are commonly used in application code:

```clojure
(export [core [*]
        primitives [bind vec-len vec-get vec-set vec-push
                    parse-int str-concat quote-sexp]])
```

The prelude is the mechanism by which standard library names become available to user modules without explicit imports (see Section 11.8).

## 11.2 Compiler-Seeded Types

Compiler-seeded types are provided by the host implementation and registered in synthetic modules during compiler initialization. They cannot be defined in user code.

Note: The types in this section (primitive types, Vec, IO, Sexp, SList) are **language-level requirements**, not standard library choices. They are normatively specified in [Section 3](03-types.md) (types), [Section 8.9](08-modules.md#89-synthetic-modules) (synthetic modules), and [Section 9.1](09-macros.md#91-sexp-data-model) (macro data model).

### 11.2.1 Primitive Types

The following types are registered in the `primitives` module:

| Type | Description | See also |
|---|---|---|
| `Int` | Signed 64-bit integer | [Section 3.1](03-types.md#31-primitive-types) |
| `Bool` | Boolean (`true` / `false`) | [Section 3.1](03-types.md#31-primitive-types) |
| `String` | Immutable UTF-8 string | [Section 3.1](03-types.md#31-primitive-types) |
| `Float` | IEEE 754 double-precision float | [Section 3.1](03-types.md#31-primitive-types) |

These types have special representation at the runtime level (see [Section 12](12-runtime.md)) and support operations through trait implementations defined in the core library, not through methods built into the types themselves.

### 11.2.2 Vec Type

```
Vec a
```

`Vec` is a built-in resizable array type, registered in the `primitives` module. It is parameterized by an element type. Vec values are created with bracket literals or the `vec` macro and manipulated through extern primitive functions.

```clojure
[1 2 3]              ; (Vec Int)
["a" "b"]            ; (Vec String)
(vec 1 2 3)          ; equivalent to [1 2 3]
```

Vec is special-cased by the compiler: its backing storage is a contiguous resizable buffer that cannot be expressed as an ADT. Operations on Vec (`vec-get`, `vec-set`, `vec-push`, `vec-len`) are implemented as extern primitives in the host language.

### 11.2.3 IO Type

```clojure
(deftype (IO a) (IOVal [:a ioval]))
```

`IO` is a compiler-seeded ADT registered in the `primitives` module. It is a single-constructor type that wraps a value to indicate an effectful computation. Functions that perform side effects MUST return `IO`. The `IOVal` constructor and `ioval` accessor are available through the module system like any other ADT.

The library functions `pure` and `bind` (Section 11.6.1) provide the fundamental monadic operations for composing IO values.

### 11.2.4 Macro Types

The following types are registered in the `macros` module:

**Sexp** -- an S-expression for compile-time macro manipulation:

```clojure
(deftype Sexp
  (SexpSym [:String sname])
  (SexpInt [:Int sval])
  (SexpFloat [:Float sval])
  (SexpBool [:Bool sval])
  (SexpStr [:String sval])
  (SexpList [:(SList Sexp) sitems])
  (SexpBracket [:(SList Sexp) sitems]))
```

**SList a** -- a polymorphic linked list for S-expression manipulation:

```clojure
(deftype (SList a)
  SNil
  (SCons [:a shead :(SList a) stail]))
```

These types are used exclusively by the macro system (see [Section 9](09-macros.md)). Macro functions receive arguments as `Sexp` values and return `Sexp` values. The `SList` type provides the list structure within `SexpList` and `SexpBracket` nodes.

## 11.3 Prelude Types (ADTs)

These algebraic data types are defined in core library modules and available through the prelude. They are ordinary ADTs -- no compiler special-casing is involved.

### 11.3.1 Option

Defined in `core.option`:

```clojure
(deftype (Option a) "An optional value, either None or Some"
  (None "Represents absence of a value")
  (Some "Wraps a present value" [:a val]))
```

`Option` represents the presence or absence of a value. It is used for operations that may fail (e.g., `parse-int`).

| Constructor | Type | Description |
|---|---|---|
| `None` | `(Option a)` | Absence of a value (nullary, bare tag) |
| `Some` | `(Fn [a] (Option a))` | Wraps a present value |
| `val` | `(Fn [(Option a)] a)` | Auto-generated field accessor |

### 11.3.2 List

Defined in `core.collections`:

```clojure
(deftype (List a) "A singly-linked immutable list"
  (Nil "The empty list")
  (Cons "A list node with head element and tail" [:a head :(List a) tail]))
```

`List` is a singly-linked immutable list. It is the standard recursive data structure for ordered sequences when random access is not needed.

| Constructor / Accessor | Type | Description |
|---|---|---|
| `Nil` | `(List a)` | Empty list (nullary, bare tag) |
| `Cons` | `(Fn [a (List a)] (List a))` | Prepend element to list |
| `head` | `(Fn [(List a)] a)` | Auto-generated field accessor |
| `tail` | `(Fn [(List a)] (List a))` | Auto-generated field accessor |

The `list` macro (Section 11.7.1) provides convenient construction syntax.

### 11.3.3 Seq

Defined in `core.sequences`:

```clojure
(deftype (Seq a) "A lazy sequence with thunked tail"
  (SeqNil "Empty lazy sequence")
  (SeqCons "Lazy sequence node with head and thunked rest"
    [:a head :(Fn [] (Seq a)) rest]))
```

`Seq` is a lazy sequence where the tail is a thunk (zero-argument closure). The tail is only evaluated when accessed, enabling representation of infinite sequences and deferred computation.

| Constructor / Accessor | Type | Description |
|---|---|---|
| `SeqNil` | `(Seq a)` | Empty sequence (nullary, bare tag) |
| `SeqCons` | `(Fn [a (Fn [] (Seq a))] (Seq a))` | Lazy cons with thunked tail |
| `head` | `(Fn [(Seq a)] a)` | Auto-generated field accessor |
| `rest` | `(Fn [(Seq a)] (Fn [] (Seq a)))` | Auto-generated field accessor (returns thunk) |

Seq values are the return type of the unified collection API (Section 11.6.4). Forcing a thunk is a regular function call: `((rest s))` forces the tail of `s`.

## 11.4 Traits

Traits define polymorphic interfaces with statically dispatched methods. All traits in the standard library are defined in core library modules and available through the prelude.

### 11.4.1 Num

Defined in `core.numerics`:

```clojure
(deftrait Num "Numeric arithmetic operations"
  (+ "Add two values" [self self] self)
  (- "Subtract two values" [self self] self)
  (* "Multiply two values" [self self] self)
  (/ "Divide two values" [self self] self))
```

| Method | Type | Description |
|---|---|---|
| `+` | `(Fn [:Num a :Num a] a)` | Addition |
| `-` | `(Fn [:Num a :Num a] a)` | Subtraction |
| `*` | `(Fn [:Num a :Num a] a)` | Multiplication |
| `/` | `(Fn [:Num a :Num a] a)` | Division |

**Implementations**: `Int`, `Float`

Int implementations delegate to inline primitives (`add-i64`, `sub-i64`, `mul-i64`, `div-i64`). Float implementations delegate to inline primitives (`add-f64`, `sub-f64`, `mul-f64`, `div-f64`). All arithmetic is prefix notation.

### 11.4.2 Eq

Defined in `core.numerics`:

```clojure
(deftrait Eq "Equality comparison"
  (= "Test equality" [self self] Bool))
```

| Method | Type | Description |
|---|---|---|
| `=` | `(Fn [:Eq a :Eq a] Bool)` | Equality test |

**Implementations**: `Int`, `Float`, `Bool`, `String`

Note: `Bool` and `String` implementations for `Eq` are provided by the compiler, not in the source-level numerics module.

### 11.4.3 Ord

Defined in `core.numerics`:

```clojure
(deftrait Ord "Ordering comparisons"
  (< "Test less-than" [self self] Bool)
  (> "Test greater-than" [self self] Bool)
  (<= "Test less-than-or-equal" [self self] Bool)
  (>= "Test greater-than-or-equal" [self self] Bool))
```

| Method | Type | Description |
|---|---|---|
| `<` | `(Fn [:Ord a :Ord a] Bool)` | Less than |
| `>` | `(Fn [:Ord a :Ord a] Bool)` | Greater than |
| `<=` | `(Fn [:Ord a :Ord a] Bool)` | Less than or equal |
| `>=` | `(Fn [:Ord a :Ord a] Bool)` | Greater than or equal |

**Implementations**: `Int`, `Float`, `String`

### 11.4.4 Display

Defined in `core.formats`:

```clojure
(deftrait Display "Convert to string representation"
  (show "Convert value to string" [self] String))
```

| Method | Type | Description |
|---|---|---|
| `show` | `(Fn [:Display a] String)` | Convert value to string |

**Implementations**: `Int`, `Float`, `Bool`, `String`

Each implementation delegates to an extern primitive:
- `Int` -> `int-to-string`
- `Float` -> `float-to-string`
- `Bool` -> `bool-to-string`
- `String` -> `string-identity` (returns the string unchanged)

### 11.4.5 Functor

Defined in `core.collections`:

```clojure
(deftrait (Functor f) "Mappable container"
  (fmap "Apply function to values inside container" [(Fn [a] b) (f a)] (f b)))
```

| Method | Type | Description |
|---|---|---|
| `fmap` | `(Fn [(Fn [a] b) (f a)] (f b))` | Map function over container |

**Implementations**: `Option`, `List`, `Seq`

Functor is a higher-kinded trait -- `f` ranges over type constructors of kind `* -> *` (see [Section 3.7](03-types.md#37-higher-kinded-types)). Implementations:

- `Option`: maps over the value inside `Some`; `None` passes through unchanged
- `List`: recursively maps over all elements, producing a new `List`
- `Seq`: lazily maps, producing a new `Seq` whose elements are computed on demand

### 11.4.6 Summary Table

| Trait | Methods | Implementations |
|---|---|---|
| `Num` | `+`, `-`, `*`, `/` | `Int`, `Float` |
| `Eq` | `=` | `Int`, `Float`, `Bool`, `String` |
| `Ord` | `<`, `>`, `<=`, `>=` | `Int`, `Float`, `String` |
| `Display` | `show` | `Int`, `Float`, `Bool`, `String` |
| `Functor` | `fmap` | `Option`, `List`, `Seq` |

## 11.5 Primitive Functions

Primitive functions are implemented in the host language (not in Cranelisp source). They are registered in synthetic modules and made available through the prelude.

### 11.5.1 Inline Primitives

Inline primitives compile to inline Cranelift IR instructions with no function call overhead. They are the implementation substrate for trait methods and are not intended to be called directly by user code.

**Integer arithmetic** -- all `(Fn [Int Int] Int)`:

| Function | Description |
|---|---|
| `add-i64` | Add two integers |
| `sub-i64` | Subtract two integers |
| `mul-i64` | Multiply two integers |
| `div-i64` | Integer division |

**Integer comparison** -- all `(Fn [Int Int] Bool)`:

| Function | Description |
|---|---|
| `eq-i64` | Test integer equality |
| `lt-i64` | Test integer less-than |
| `gt-i64` | Test integer greater-than |
| `le-i64` | Test integer less-than-or-equal |
| `ge-i64` | Test integer greater-than-or-equal |

**Float arithmetic** -- all `(Fn [Float Float] Float)`:

| Function | Description |
|---|---|
| `add-f64` | Add two floats |
| `sub-f64` | Subtract two floats |
| `mul-f64` | Multiply two floats |
| `div-f64` | Float division |

**Float comparison** -- all `(Fn [Float Float] Bool)`:

| Function | Description |
|---|---|
| `eq-f64` | Test float equality |
| `lt-f64` | Test float less-than |
| `gt-f64` | Test float greater-than |
| `le-f64` | Test float less-than-or-equal |
| `ge-f64` | Test float greater-than-or-equal |

### 11.5.2 Extern Primitives

Extern primitives are host-language functions called via the foreign function interface. They are registered in the `primitives` module.

**Type conversion**:

| Function | Type | Description |
|---|---|---|
| `int-to-string` | `(Fn [Int] String)` | Convert integer to string representation |
| `float-to-string` | `(Fn [Float] String)` | Convert float to string representation |
| `bool-to-string` | `(Fn [Bool] String)` | Convert boolean to string representation |
| `string-identity` | `(Fn [String] String)` | Return string unchanged (Display impl for String) |

**String operations**:

| Function | Type | Description |
|---|---|---|
| `str-concat` | `(Fn [String String] String)` | Concatenate two strings |

**Parsing**:

| Function | Type | Description |
|---|---|---|
| `parse-int` | `(Fn [String] (Option Int))` | Parse string as integer; returns `None` on failure |

**Macro support**:

| Function | Type | Description |
|---|---|---|
| `quote-sexp` | `(Fn [Sexp] Sexp)` | Convert Sexp value to constructor source code |

**Vec operations**:

| Function | Type | Description |
|---|---|---|
| `vec-get` | `(Fn [(Vec a) Int] a)` | Return element at index (bounds-checked) |
| `vec-set` | `(Fn [(Vec a) Int a] (Vec a))` | Return new Vec with element at index replaced |
| `vec-push` | `(Fn [(Vec a) a] (Vec a))` | Return new Vec with element appended |
| `vec-len` | `(Fn [(Vec a)] Int)` | Return number of elements |
| `vec-map` | `(Fn [(Fn [a] b) (Vec a)] (Vec b))` | Apply function to each element, return new Vec |
| `vec-reduce` | `(Fn [(Fn [b a] b) b (Vec a)] b)` | Left fold over Vec elements |

Vec operations are polymorphic (quantified over the element type). `vec-get` performs bounds checking and panics on out-of-bounds access. `vec-set` and `vec-push` return new Vec values (semantically immutable; the implementation MAY use copy-on-write when the reference count is 1).

### 11.5.3 Platform Primitives

Platform primitives are provided by platform DLLs (see [Section 10](10-io.md)). The default `stdio` platform provides:

| Function | Type | Description |
|---|---|---|
| `print` | `(Fn [String] (IO Int))` | Print string followed by newline; returns 0 |
| `read-line` | `(Fn [] (IO String))` | Read a line from stdin (trims trailing newline) |

Platform functions MUST return `IO` -- this is validated at platform registration time. Platform functions are registered in a `platform.<name>` module and made available through import.

## 11.6 Library Functions

Library functions are defined in Cranelisp source in the core library modules. They are ordinary functions -- no compiler special-casing is involved.

### 11.6.1 IO Operations (core.io)

```clojure
(defn pure "Lift a value into IO" [x] (IOVal x))
```

`pure :: (Fn [a] (IO a))`

Wraps a value in `IO` by constructing an `IOVal`. Used when a pure value must be returned in an IO context (e.g., in an `if` branch where the other branch performs IO).

```clojure
(defn bind "Chain IO actions, passing result of first to second" [io cont]
  (match io
    [(IOVal v) (cont v)]))
```

`bind :: (Fn [(IO a) (Fn [a] (IO b))] (IO b))`

Extracts the value from an `IO a` and passes it to a continuation function `a -> IO b`. This is the fundamental sequencing operation for IO computations. The `bind!` macro (Section 11.7.4) provides syntactic sugar for chaining multiple binds.

### 11.6.2 Numeric Functions (core.numerics)

```clojure
(defn inc "Increment by one" [:Int x] (+ x 1))
```

`inc :: (Fn [Int] Int)`

Increments an integer by 1. Annotated with `:Int` to produce a monomorphic function rather than a constrained polymorphic one.

### 11.6.3 List Operations (core.collections)

```clojure
(defn empty? "Returns true if list is empty" [xs]
  (match xs [Nil true  _ false]))
```

`empty? :: (Fn [(List a)] Bool)`

Returns `true` if the list is `Nil`, `false` otherwise.

---

```clojure
(defn concat "Concatenate two lists" [xs ys]
  (match xs [Nil ys  (Cons h t) (Cons h (concat t ys))]))
```

`concat :: (Fn [(List a) (List a)] (List a))`

Concatenates two lists. The first list is traversed; the second list becomes the tail. O(n) in the length of the first list.

---

```clojure
(defn list-reduce "Reduce a list with function and initial accumulator" [f init xs]
  (match xs [Nil init  (Cons h t) (list-reduce f (f init h) t)]))
```

`list-reduce :: (Fn [(Fn [b a] b) b (List a)] b)`

Left fold over a list. Applies the reducer function to the accumulator and each element, left to right. Self-tail-recursive (benefits from TCO).

---

```clojure
(defn reverse "Reverse a list" [xs]
  (list-reduce (fn [acc x] (Cons x acc)) Nil xs))
```

`reverse :: (Fn [(List a)] (List a))`

Reverses a list. Implemented as a left fold, building a new list by prepending each element.

### 11.6.4 Unified Collection API (core.sequences)

The unified collection API provides functions that operate on any of the three collection types: `Vec`, `List`, or `Seq`. All functions use multi-signature dispatch (see [Section 4.7](04-expressions.md#47-multi-signature-dispatch)) to select the appropriate variant based on the collection argument's type.

`map`, `filter`, `take`, and `drop` return lazy `Seq` values -- elements are computed on demand. `reduce` is eager -- it forces the entire collection.

**map**

```clojure
(defn map "Apply function to each element, returning lazy sequence"
  ([f v] (fmap f (vec-to-seq 0 v)))      ; v : (Vec a)
  ([f l] (fmap f (list-to-seq l)))        ; l : (List a)
  ([f s] (fmap f s)))                     ; s : (Seq a)
```

`map :: (Fn [(Fn [a] b) (Vec a)] (Seq b))` | `(Fn [(Fn [a] b) (List a)] (Seq b))` | `(Fn [(Fn [a] b) (Seq a)] (Seq b))`

Lazily applies a function to each element of a collection, returning a `Seq`.

---

**filter**

```clojure
(defn filter "Return lazy sequence of elements matching predicate"
  ([pred v] (lazy-filter pred (vec-to-seq 0 v)))
  ([pred l] (lazy-filter pred (list-to-seq l)))
  ([pred s] (lazy-filter pred s)))
```

`filter :: (Fn [(Fn [a] Bool) (Vec a)] (Seq a))` | `(Fn [(Fn [a] Bool) (List a)] (Seq a))` | `(Fn [(Fn [a] Bool) (Seq a)] (Seq a))`

Lazily filters a collection, keeping elements for which the predicate returns `true`.

---

**take**

```clojure
(defn take "Take first n elements as lazy sequence"
  ([:Int n v] (lazy-take n (vec-to-seq 0 v)))
  ([:Int n l] (lazy-take n (list-to-seq l)))
  ([:Int n s] (lazy-take n s)))
```

`take :: (Fn [Int (Vec a)] (Seq a))` | `(Fn [Int (List a)] (Seq a))` | `(Fn [Int (Seq a)] (Seq a))`

Returns a lazy sequence of at most `n` elements from the beginning of the collection.

---

**drop**

```clojure
(defn drop "Drop first n elements, return rest as lazy sequence"
  ([:Int n v] (lazy-drop n (vec-to-seq 0 v)))
  ([:Int n l] (lazy-drop n (list-to-seq l)))
  ([:Int n s] (lazy-drop n s)))
```

`drop :: (Fn [Int (Vec a)] (Seq a))` | `(Fn [Int (List a)] (Seq a))` | `(Fn [Int (Seq a)] (Seq a))`

Drops the first `n` elements and returns the rest as a lazy sequence. Note that `drop` on a Seq is eager in the dropped elements -- it forces `n` thunks immediately.

---

**reduce**

```clojure
(defn reduce "Reduce collection to single value with function and initial accumulator"
  ([f init v] (lazy-reduce f init (vec-to-seq 0 v)))
  ([f init l] (lazy-reduce f init (list-to-seq l)))
  ([f init s] (lazy-reduce f init s)))
```

`reduce :: (Fn [(Fn [b a] b) b (Vec a)] b)` | `(Fn [(Fn [b a] b) b (List a)] b)` | `(Fn [(Fn [b a] b) b (Seq a)] b)`

Eager left fold over a collection. Forces the entire collection. MUST NOT be called on an infinite Seq -- it will not terminate.

---

**seq**

```clojure
(defn seq "Convert collection to lazy sequence"
  ([v] (vec-to-seq 0 v))       ; v : (Vec a)
  ([l] (list-to-seq l)))       ; l : (List a)
```

`seq :: (Fn [(Vec a)] (Seq a))` | `(Fn [(List a)] (Seq a))`

Converts a `Vec` or `List` to a lazy `Seq`. The resulting Seq produces elements on demand.

### 11.6.5 Seq Producers (core.sequences)

These functions create lazy sequences, potentially infinite:

```clojure
(defn range-from "Infinite lazy sequence starting at n" [:Int n]
  (SeqCons n (fn [] (range-from (+ n 1)))))
```

`range-from :: (Fn [Int] (Seq Int))`

Produces an infinite lazy sequence of integers: `n`, `n+1`, `n+2`, ...

---

```clojure
(defn iterate "Infinite lazy sequence: x, (f x), (f (f x)), ..." [f x]
  (SeqCons x (fn [] (iterate f (f x)))))
```

`iterate :: (Fn [(Fn [a] a) a] (Seq a))`

Produces an infinite lazy sequence by repeated function application: `x`, `(f x)`, `(f (f x))`, ...

---

```clojure
(defn repeat "Infinite lazy sequence of x" [x]
  (SeqCons x (fn [] (repeat x))))
```

`repeat :: (Fn [a] (Seq a))`

Produces an infinite lazy sequence where every element is `x`.

### 11.6.6 Seq Internal Operations (core.sequences)

These functions operate directly on `Seq` values. They are used internally by the unified collection API but are also available as public functions.

```clojure
(defn lazy-filter "Filter a lazy sequence by predicate" [pred s] ...)
```

`lazy-filter :: (Fn [(Fn [a] Bool) (Seq a)] (Seq a))`

Lazily filters a sequence. May force multiple thunks to find the next matching element.

---

```clojure
(defn lazy-take "Take first n elements from lazy sequence" [:Int n s] ...)
```

`lazy-take :: (Fn [Int (Seq a)] (Seq a))`

Returns a lazy sequence of at most `n` elements.

---

```clojure
(defn lazy-drop "Drop first n elements from lazy sequence" [:Int n s] ...)
```

`lazy-drop :: (Fn [Int (Seq a)] (Seq a))`

Eagerly forces and discards `n` elements, then returns the rest.

---

```clojure
(defn lazy-reduce "Reduce a lazy sequence with function and initial accumulator" [f init s] ...)
```

`lazy-reduce :: (Fn [(Fn [b a] b) b (Seq a)] b)`

Eager left fold over an entire lazy sequence. Will not terminate on infinite sequences.

### 11.6.7 Seq Conversions (core.sequences)

```clojure
(defn to-list "Force entire lazy sequence into a list" [s] ...)
```

`to-list :: (Fn [(Seq a)] (List a))`

Eagerly materializes an entire lazy sequence into a `List`. MUST NOT be called on an infinite Seq -- it will not terminate.

---

```clojure
(defn vec-to-seq "Convert vec to lazy sequence starting at index" [:Int idx v] ...)
```

`vec-to-seq :: (Fn [Int (Vec a)] (Seq a))`

Internal function: converts a `Vec` to a lazy `Seq` starting at the given index. Used by the unified collection API. The first argument is the starting index (normally 0).

---

```clojure
(defn list-to-seq "Convert list to lazy sequence" [xs] ...)
```

`list-to-seq :: (Fn [(List a)] (Seq a))`

Internal function: converts a `List` to a lazy `Seq`. Used by the unified collection API.

### 11.6.8 SList Helper Functions (core.syntax)

These functions operate on the `SList` type from the `macros` module. They are primarily used within macro definitions. None are re-exported through the prelude — the `~@` quasiquote operator uses `sconcat` via qualified reference (`core.syntax/sconcat`). All four helpers are public in `core.syntax` for use by sibling modules like `core.derive`, but not re-exported to the prelude namespace.

```clojure
(defn sfold "Fold over an SList" [f init xs] ...)
```

`sfold :: (Fn [(Fn [b a] b) b (SList a)] b)`

Left fold over an `SList`. Used by macro implementations to process argument lists.

---

```clojure
(defn sreverse "Reverse an SList" [xs] ...)
```

`sreverse :: (Fn [(SList a)] (SList a))`

Reverses an `SList`. Implemented using `sfold`.

---

```clojure
(defn sconcat "Concatenate two SLists" [xs ys] ...)
```

`sconcat :: (Fn [(SList a) (SList a)] (SList a))`

Concatenates two `SList` values.

---

```clojure
(defn sempty? "Test if an SList is empty" [xs] ...)
```

`sempty? :: (Fn [(SList a)] Bool)`

Returns `true` if the `SList` is `SNil`.

## 11.7 Prelude Macros

All macros are defined in `core.syntax` and available through the prelude. Macros are expanded at compile time before type checking. Each macro receives its arguments as `Sexp` values and returns a `Sexp` value.

### 11.7.1 list -- List Construction

```clojure
(defmacro list "Construct a list from elements" [& elems] ...)
```

`list :: macro [& elems] -> Sexp`

Expands to nested `Cons`/`Nil` constructor calls:

```clojure
(list 1 2 3)
;; expands to:
(Cons 1 (Cons 2 (Cons 3 Nil)))
```

### 11.7.2 slist -- SList Construction

```clojure
(defmacro slist "Construct an SList from elements" [& elems] ...)
```

`slist :: macro [& elems] -> Sexp`

Expands to nested `SCons`/`SNil` constructor calls. Used in macro bodies to build `SList` values for `SexpList` or `SexpBracket` nodes.

```clojure
(slist (SexpSym "+") x (SexpInt 1))
;; expands to:
(SCons (SexpSym "+") (SCons x (SCons (SexpInt 1) SNil)))
```

### 11.7.3 do -- Expression Sequencing

```clojure
(defmacro do "Sequence expressions, return last value" [& body] ...)
```

`do :: macro [& body] -> Sexp`

Expands to nested `let` bindings with discarded results. The last expression's value is returned.

```clojure
(do (print "a") (print "b") (print "c"))
;; expands to:
(let [_ (print "a")]
  (let [_ (print "b")]
    (print "c")))
```

### 11.7.4 bind! -- Monadic Bind Sugar

```clojure
(defmacro bind! "Monadic bind sugar" [bindings body] ...)
```

`bind! :: macro [bindings body] -> Sexp`

Desugars to nested `bind`/`fn` calls. The `bindings` argument is a bracket form containing alternating name/expression pairs:

```clojure
(bind! [line (read-line)
        n    (pure (parse-int line))]
  (match n
    [(Some x) (print (show x))
     None     (print "parse failed")]))

;; expands to:
(bind (read-line) (fn [line]
  (bind (pure (parse-int line)) (fn [n]
    (match n
      [(Some x) (print (show x))
       None     (print "parse failed")])))))
```

### 11.7.5 vec -- Vec Construction

```clojure
(defmacro vec "Construct a vec from elements" [& elems] ...)
```

`vec :: macro [& elems] -> Sexp`

Expands to a bracket form `[e1 e2 ...]`, which is the Vec literal syntax:

```clojure
(vec 1 2 3)
;; expands to:
[1 2 3]
```

### 11.7.6 str -- String Interpolation

```clojure
(defmacro str "Concatenate string representations of all arguments" [& args] ...)
```

`str :: macro [& args] -> Sexp`

Converts each argument to a string via `show` and concatenates the results with `str-concat`:

```clojure
(str "x=" x " y=" y)
;; expands to:
(str-concat (show "x=") (str-concat (show x) (str-concat (show " y=") (show y))))
```

With zero arguments, expands to the empty string `""`.

### 11.7.7 cond -- Multi-Way Conditional

```clojure
(defmacro cond "Multi-way conditional with mandatory default" [& clauses] ...)
```

`cond :: macro [& clauses] -> Sexp`

Expands to nested `if` expressions. Clauses are alternating condition/body pairs. The last clause (odd position) is the mandatory default:

```clojure
(cond (< x 0) "negative"
      (= x 0) "zero"
      "positive")
;; expands to:
(if (< x 0) "negative"
  (if (= x 0) "zero"
    "positive"))
```

### 11.7.8 case -- Value Dispatch

```clojure
(defmacro case "Dispatch on value equality with mandatory default" [expr & clauses] ...)
```

`case :: macro [expr & clauses] -> Sexp`

Evaluates `expr` once, then dispatches on equality. Expands to a `let` binding the expression to an internal name, followed by nested `if`/`=` tests:

```clojure
(case color
  "red"   1
  "green" 2
  "blue"  3
  0)
;; expands to:
(let [__case__ color]
  (if (= __case__ "red") 1
    (if (= __case__ "green") 2
      (if (= __case__ "blue") 3
        0))))
```

The last clause (odd position) is the mandatory default.

### 11.7.9 -> -- Thread First

```clojure
(defmacro -> "Thread value through forms as first argument" [x & forms] ...)
```

`-> :: macro [x & forms] -> Sexp`

Threads a value through a series of function calls as the **first** argument. If a form is a bare symbol, it is treated as a unary function call. If a form is a list, the threaded value is inserted after the function name:

```clojure
(-> 5 inc (* 2) (+ 10))
;; expands to:
(+ (* (inc 5) 2) 10)
```

Step by step: `5` -> `(inc 5)` -> `(* (inc 5) 2)` -> `(+ (* (inc 5) 2) 10)`.

### 11.7.10 ->> -- Thread Last

```clojure
(defmacro ->> "Thread value through forms as last argument" [x & forms] ...)
```

`->> :: macro [x & forms] -> Sexp`

Threads a value through a series of function calls as the **last** argument:

```clojure
(->> [1 2 3] (map inc) (take 2) to-list)
;; expands to:
(to-list (take 2 (map inc [1 2 3])))
```

### 11.7.11 const -- Named Constant

```clojure
(defmacro const "Define a named constant (bare symbol expansion)" [name value] ...)
```

`const :: macro [name value] -> Sexp`

Defines a compile-time constant. The value is captured at definition time via `quote-sexp` and substituted inline wherever the name appears (via zero-arg macro bare-symbol expansion):

```clojure
(const PI 3.14)
(* PI 2.0)          ; expands to (* 3.14 2.0)
```

`const-` creates a module-private constant.

### 11.7.12 def -- Named Value

```clojure
(defmacro def "Define a named value (zero-arg function, bare symbol)" [name value] ...)
```

`def :: macro [name value] -> Sexp`

Defines a named value. Expands to a `begin` containing a zero-arg function definition (with a mangled name) and a macro that calls it:

```clojure
(def ten (+ 5 5))
;; expands to:
(begin
  (defn ten-def [] (+ 5 5))
  (defmacro ten [] (SexpList (SCons (SexpSym "ten-def") SNil))))

ten                 ; expands to (ten-def), evaluates to 10
```

Unlike `const`, the value expression is evaluated at runtime (as a zero-arg function call). This is suitable for values that involve computation.

`def-` creates a module-private value.

## 11.8 Implicit Prelude Import

The normative implicit import rule is defined in [Section 8.8](08-modules.md#88-prelude). In brief: when a `prelude` module is found, the compiler injects `(import [prelude [*]])` for every source-level module except the prelude itself. An explicit `(import [prelude [...]])` replaces the implicit glob import.

The reference implementation's prelude re-exports all names from `core` plus selected primitives (Section 11.1.3), making the types, traits, functions, and macros described in this section available as bare names in every user module.
