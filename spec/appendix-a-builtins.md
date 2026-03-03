# Appendix A: Builtin Reference (Non-Normative)

> **This appendix is non-normative.** It documents the reference implementation's compiler-seeded types and primitive functions. Sections A.1–A.2 describe types that are language-level requirements (normatively specified in [Section 3](03-types.md) and [Section 8.9](08-modules.md#89-synthetic-modules)). Sections A.3–A.4 list primitive functions and special forms provided by the reference implementation.

## A.1 Primitive Types

Registered in the `primitives` module. Available in all programs via `(import [primitives [*]])` or qualified reference.

| Type | Description | Value Domain |
|---|---|---|
| `Int` | Signed 64-bit integer | -2^63 to 2^63 - 1 |
| `Bool` | Boolean | `true`, `false` |
| `String` | Immutable UTF-8 string | Heap-allocated byte sequence |
| `Float` | IEEE 754 double-precision | 64-bit floating point |

## A.2 Built-in Compound Types

Registered in the `primitives` and `macros` synthetic modules.

| Type | Module | Kind | Description |
|---|---|---|---|
| `(Vec a)` | `primitives` | Built-in | Resizable array, element access via extern primitives |
| `(IO a)` | `primitives` | Compiler-seeded ADT | Effectful computation; constructors `Pure`, `Effect`, `Bind` |
| `Sexp` | `macros` | Compiler-seeded ADT | S-expression value for macro system |
| `(SList a)` | `macros` | Compiler-seeded ADT | Cons-list for S-expression manipulation |

## A.3 Primitive Functions (Host-Implemented)

Primitive functions are implemented in the host language and registered in the `primitives` module. They are the low-level substrate; standard library functions and trait implementations are built on top of them.

### Inline Primitives

Inline primitives compile to inline Cranelift IR instructions — no function call overhead.

**Integer arithmetic** — all `(Fn [Int Int] Int)`:

| Function | Description |
|---|---|
| `add-i64` | Add |
| `sub-i64` | Subtract |
| `mul-i64` | Multiply |
| `div-i64` | Integer division |

**Integer comparison** — all `(Fn [Int Int] Bool)`:

| Function | Description |
|---|---|
| `eq-i64` | Equality |
| `lt-i64` | Less than |
| `gt-i64` | Greater than |
| `le-i64` | Less than or equal |
| `ge-i64` | Greater than or equal |

**Float arithmetic** — all `(Fn [Float Float] Float)`:

| Function | Description |
|---|---|
| `add-f64` | Add |
| `sub-f64` | Subtract |
| `mul-f64` | Multiply |
| `div-f64` | Division |

**Float comparison** — all `(Fn [Float Float] Bool)`:

| Function | Description |
|---|---|
| `eq-f64` | Equality |
| `lt-f64` | Less than |
| `gt-f64` | Greater than |
| `le-f64` | Less than or equal |
| `ge-f64` | Greater than or equal |

### Extern Primitives

Extern primitives are called via the foreign function interface.

**Type conversion**:

| Function | Type | Description |
|---|---|---|
| `int-to-string` | `(Fn [Int] String)` | Convert integer to decimal string |
| `float-to-string` | `(Fn [Float] String)` | Convert float to string |
| `bool-to-string` | `(Fn [Bool] String)` | `"true"` or `"false"` |
| `string-identity` | `(Fn [String] String)` | Identity for `String` (used by Display impl) |

**String operations**:

| Function | Type | Description |
|---|---|---|
| `str-concat` | `(Fn [String String] String)` | Concatenate two strings |
| `parse-int` | `(Fn [String] (Option Int))` | Parse decimal integer; `None` on failure |

**Macro support**:

| Function | Type | Description |
|---|---|---|
| `quote-sexp` | `(Fn [Sexp] Sexp)` | Convert a runtime `Sexp` value to constructor source code |

**Vec operations**:

| Function | Type | Description |
|---|---|---|
| `vec-get` | `(Fn [(Vec a) Int] a)` | Index (bounds-checked; panics on out-of-bounds) |
| `vec-set` | `(Fn [(Vec a) Int a] (Vec a))` | Return new Vec with element at index replaced |
| `vec-push` | `(Fn [(Vec a) a] (Vec a))` | Return new Vec with element appended |
| `vec-len` | `(Fn [(Vec a)] Int)` | Number of elements |
| `vec-map` | `(Fn [(Fn [a] b) (Vec a)] (Vec b))` | Map function over elements |
| `vec-reduce` | `(Fn [(Fn [b a] b) b (Vec a)] b)` | Left fold over elements |

`vec-set` and `vec-push` are semantically pure (return new values). The implementation MAY use copy-on-write when the reference count is 1.

## A.4 Special Forms

Special forms are keywords processed directly by the compiler. They are not functions or macros and cannot be shadowed.

| Form | Description |
|---|---|
| `defn` / `defn-` | Function definition (single or multi-sig); `defn-` is module-private |
| `deftype` / `deftype-` | Algebraic data type definition; `deftype-` is module-private |
| `deftrait` / `deftrait-` | Trait declaration; `deftrait-` is module-private |
| `impl` | Trait implementation |
| `defmacro` / `defmacro-` | Macro definition; `defmacro-` is module-private |
| `let` | Local bindings: `(let [x e1 y e2] body)` |
| `if` | Conditional: `(if cond then else)` |
| `fn` | Lambda expression: `(fn [params] body)` |
| `match` | Pattern matching: `(match scrutinee [pat1 body1 ...])` |
| `mod` / `mod-` | Submodule declaration; `mod-` is module-private |
| `import` | Name import: `(import [module [names]])` |
| `export` | Name re-export: `(export [module [names]])` |
| `platform` | Platform DLL declaration (entry module only): `(platform stdio)` |
