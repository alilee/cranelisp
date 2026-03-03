# Appendix A: Builtin Reference (Non-Normative)

> **This appendix is non-normative.** It documents the reference implementation's standard environment. Compiler-seeded types (Sections A.1, A.2) are language-level requirements specified normatively in [Sections 3](03-types.md) and [8.9](08-modules.md#89-synthetic-modules). Everything else (Sections A.3-A.7) describes the reference implementation's standard library choices.

Complete reference for all types, traits, functions, and macros available in the reference implementation's standard Cranelisp environment.

## A.1 Primitive Types

| Type | Description | Value Domain |
|---|---|---|
| `Int` | Signed 64-bit integer | -2^63 to 2^63 - 1 |
| `Bool` | Boolean | `true`, `false` |
| `String` | UTF-8 string | Immutable byte sequence |
| `Float` | IEEE 754 double-precision | 64-bit floating point |

## A.2 Built-in Compound Types

| Type | Kind | Description |
|---|---|---|
| `(Vec a)` | Built-in | Resizable array |
| `(IO a)` | Compiler-seeded ADT | Effectful computation |
| `Sexp` | Compiler-seeded ADT | S-expression values (for macros) |
| `(SList a)` | Compiler-seeded ADT | Macro-internal list |

## A.3 Prelude Types — Reference Implementation (ADTs)

| Type | Constructors | Description |
|---|---|---|
| `(Option a)` | `None`, `(Some [:a val])` | Optional value |
| `(List a)` | `Nil`, `(Cons [:a head :(List a) tail])` | Linked list |
| `(Seq a)` | `SeqNil`, `(SeqCons [:a head :(Fn [] (Seq a)) rest])` | Lazy sequence |

## A.4 Traits — Reference Implementation

| Trait | Methods | Implementations |
|---|---|---|
| `Num` | `+`, `-`, `*`, `/` | Int, Float |
| `Eq` | `=` | Int, Float, Bool, String |
| `Ord` | `<`, `>`, `<=`, `>=` | Int, Float, String |
| `Display` | `show` | Int, Float, Bool, String |
| `Functor` | `fmap` | Option, List, Seq |

## A.5 Primitive Functions (Host-Implemented)

### Arithmetic (Inline)

| Function | Type | Description |
|---|---|---|
| `+` | `Num a => a -> a -> a` | Addition |
| `-` | `Num a => a -> a -> a` | Subtraction |
| `*` | `Num a => a -> a -> a` | Multiplication |
| `/` | `Num a => a -> a -> a` | Division |

### Comparison (Inline)

| Function | Type | Description |
|---|---|---|
| `=` | `Eq a => a -> a -> Bool` | Equality |
| `<` | `Ord a => a -> a -> Bool` | Less than |
| `>` | `Ord a => a -> a -> Bool` | Greater than |
| `<=` | `Ord a => a -> a -> Bool` | Less or equal |
| `>=` | `Ord a => a -> a -> Bool` | Greater or equal |

### Type Conversion (Extern)

| Function | Type | Description |
|---|---|---|
| `show` | `Display a => a -> String` | Convert to string |
| `parse-int` | `String -> (Option Int)` | Parse integer (pure) |

### String Operations (Extern)

| Function | Type | Description |
|---|---|---|
| `str-concat` | `String -> String -> String` | Concatenate two strings |
| `quote-sexp` | `Sexp -> Sexp` | Quote a Sexp value |

### Vec Operations (Extern)

| Function | Type | Description |
|---|---|---|
| `vec-get` | `(Vec a) -> Int -> a` | Index (bounds-checked) |
| `vec-set` | `(Vec a) -> Int -> a -> (Vec a)` | Set element at index |
| `vec-push` | `(Vec a) -> a -> (Vec a)` | Append element |
| `vec-len` | `(Vec a) -> Int` | Length |
| `vec-map` | `(a -> b) -> (Vec a) -> (Vec b)` | Map over Vec |
| `vec-reduce` | `(b -> a -> b) -> b -> (Vec a) -> b` | Left fold over Vec |

### Platform Functions (stdio)

| Function | Type | Description |
|---|---|---|
| `print` | `String -> IO Int` | Print with newline, returns 0 |
| `read-line` | `(Fn [] (IO String))` | Read line from stdin |

## A.6 Library Functions — Reference Implementation (Cranelisp-Defined)

### IO (core.io)

| Function | Type | Description |
|---|---|---|
| `pure` | `a -> IO a` | Lift value into IO |
| `bind` | `IO a -> (a -> IO b) -> IO b` | Monadic bind |

### Numeric (core.numerics)

| Function | Type | Description |
|---|---|---|
| `inc` | `Int -> Int` | Increment by 1 |

### List Operations (core.collections)

| Function | Type | Description |
|---|---|---|
| `empty?` | `(List a) -> Bool` | Test for Nil |
| `concat` | `(List a) -> (List a) -> (List a)` | Concatenate lists |
| `list-map` | `(a -> b) -> (List a) -> (List b)` | Map over List |
| `list-reduce` | `(b -> a -> b) -> b -> (List a) -> b` | Left fold over List |
| `reverse` | `(List a) -> (List a)` | Reverse a list |

### Unified Collection API (core.sequences, multi-sig)

| Function | Type | Description |
|---|---|---|
| `map` | `(a -> b) -> C -> (Seq b)` | Lazy map (C = Vec, List, or Seq) |
| `filter` | `(a -> Bool) -> C -> (Seq a)` | Lazy filter |
| `take` | `Int -> C -> (Seq a)` | Lazy take first N |
| `drop` | `Int -> C -> (Seq a)` | Lazy drop first N |
| `reduce` | `(b -> a -> b) -> b -> C -> b` | Eager left fold |
| `seq` | `C -> (Seq a)` | Convert to lazy Seq (C = Vec or List) |

### Seq Producers (core.sequences)

| Function | Type | Description |
|---|---|---|
| `range-from` | `Int -> (Seq Int)` | Infinite integer sequence from N |
| `iterate` | `(a -> a) -> a -> (Seq a)` | Infinite repeated application |
| `repeat` | `a -> (Seq a)` | Infinite repetition |

### Seq Consumers (core.sequences)

| Function | Type | Description |
|---|---|---|
| `to-list` | `(Seq a) -> (List a)` | Materialize to List (eager) |

### SList Helpers (core.syntax)

| Function | Type | Description |
|---|---|---|
| `sfold` | `(b -> a -> b) -> b -> (SList a) -> b` | Left fold over SList |
| `sreverse` | `(SList a) -> (SList a)` | Reverse an SList |
| `sconcat` | `(SList a) -> (SList a) -> (SList a)` | Concatenate SLists |
| `sempty?` | `(SList a) -> Bool` | Test for SNil |

## A.7 Prelude Macros — Reference Implementation

| Macro | Parameters | Expansion |
|---|---|---|
| `list` | `& elems` | `(Cons e1 (Cons e2 ... Nil))` |
| `slist` | `& elems` | `(SCons e1 (SCons e2 ... SNil))` |
| `do` | `& exprs` | `(let [_ e1] (let [_ e2] ... en))` |
| `bind!` | `bindings body` | `(bind e1 (fn [x] (bind e2 (fn [y] body))))` |
| `vec` | `& elems` | Vec literal |
| `str` | `& exprs` | `(str-concat (show e1) (str-concat (show e2) ...))` |
| `cond` | `& pairs` | `(if c1 e1 (if c2 e2 ... en))` |
| `case` | `x & pairs` | `(if (= x v1) e1 (if (= x v2) e2 ... en))` |
| `->` | `x & forms` | Thread-first: `(f2 (f1 x) ...)` |
| `->>` | `x & forms` | Thread-last: `(f2 ... (f1 ... x))` |
| `const` | `name val` | Inline substitution (zero-arg macro) |
| `def` | `name val` | Zero-arg function + call macro |

## A.8 Special Forms

| Form | Description |
|---|---|
| `defn` / `defn-` | Function definition (single or multi-sig) |
| `deftype` / `deftype-` | Algebraic data type definition |
| `deftrait` / `deftrait-` | Trait declaration |
| `impl` | Trait implementation |
| `defmacro` / `defmacro-` | Macro definition |
| `let` | Local bindings |
| `if` | Conditional |
| `fn` | Lambda expression |
| `match` | Pattern matching |
| `mod` | Submodule declaration |
| `import` | Name import |
| `export` | Name re-export |
| `platform` | Platform DLL declaration |
