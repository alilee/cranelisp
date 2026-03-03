# REPL Display Format

## Design Principle

Every symbol and expression entered at the REPL produces useful feedback — its type, value, or usage description. No valid language construct produces an opaque error. Special forms, operators, builtins, and user-defined names all respond with what they are and how to use them.

Feedback reinforces the language syntax, using cranelisp type notation (e.g. `if :: special form: (Fn [Bool a a] a)`).

## Decision Tree

When the REPL receives input that parses as a bare expression:

```
Is it a Var (bare name)?
├── Yes: Is it a special form?
│   ├── Yes → special_form_description()    "if :: special form: ..."
│   └── No: Is it a loaded module name?
│       ├── Yes → print module info          "Module 'util':\n  helper :: ..."
│       └── No: Is it a macro name?
│           ├── Yes → format_macro_type()    "list :: (macro [& elems] Sexp)"
│           └── No: Does describe_symbol() return Some?
│               ├── Yes → format_symbol_info()  "foo :: (Fn [Int] Int)"
│               └── No → typecheck, compile, execute → format value
└── No: typecheck, compile, execute → format value
```

Definitions (`defn`, `deftype`, `deftrait`, `impl`) print their own confirmation and return.

## Symbol Lookup Order

`describe_symbol()` in `src/typechecker/introspect.rs` uses a 4-step classification:

1. **Dotted name** — `Type.Constructor` or `Trait.method` delegation
2. **User-defined type** — `resolve_type_def_via_modules` (e.g. `Option`, `Point`, `Color`)
3. **Builtin type** — `impls_for_type` (e.g. `Int`, `Bool`, `String`, `Float`)
4. **Entry-based classification** — single `lookup_entry_via_modules` call, then match on `ModuleEntry` variant:
   - `TraitDecl` → trait declaration (e.g. `Display`, `Num`)
   - `Constructor` → data constructor (e.g. `Some`, `None`, `Cons`)
   - `Def` with inline primitive meta → inline primitive (e.g. `add-i64`)
   - `Def` with extern/platform meta → extern primitive (e.g. `int-to-string`)
   - `Def` with `constrained_fn` → constrained polymorphic fn (e.g. user `add`)
   - `Def` + `method_to_trait` → trait method or operator (e.g. `show`, `+`)
   - `Def` + `overloads` → overloaded multi-sig fn (e.g. `map`, `filter`)
   - `Def` with `Fn` type → plain user function (e.g. `empty?`)

If none match, returns `None` → the expression is compiled and evaluated.

## Format Table

All display formats use the pattern `name :: description`. The `name` may be qualified with a namespace prefix for disambiguation.

| # | Category | SymbolInfo Variant | Format | Example |
|---|----------|-------------------|--------|---------|
| 1 | Special form | (none — `special_form_description`) | `name :: special form: description` | `if :: special form: (Fn [Bool a a] a)` |
| 2 | Top-level form | (none — `special_form_description`) | `name :: top-level form: description` | `defn :: top-level form: (defn name [params...] body)` |
| 3 | Sugar | (none — `special_form_description`) | `name :: sugar: description` | `list :: sugar: (list e1 e2 ...) — constructs a List from elements` |
| 4 | Trait declaration | `TraitDecl` | `name :: (deftrait ...)` | `Display :: (deftrait Display (show [self] String))` |
| 5 | Trait declaration (with impls) | `TraitDecl` | `name :: (deftrait ...) \| impl T1, T2` | `Num :: (deftrait Num ...) \| impl Int, Float` |
| 6 | Built-in type | `TypeName` | `name :: type \| impl T1, T2` | `Int :: type \| impl Display, Num, Eq, Ord` |
| 7 | User-defined type | `UserType` | `name :: (deftype ...)` | `Option :: (deftype (Option a) None (Some [:a val]))` |
| 8 | Operator method | `OperatorMethod` | `Trait.name :: (Fn [...] ...)` | `Num.+ :: (Fn [:Num a a] a)` |
| 9 | Trait method | `TraitMethod` | `Trait.name :: (Fn [...] ...)` | `Display.show :: (Fn [:Display a] String)` |
| 9b | HKT trait method | `TraitMethod` | `Trait.name :: (Fn [...] ...)` | `Functor.fmap :: (Fn [(Fn [a] b) (:Functor f a)] (f b))` |
| 10 | Inline primitive | `InlinePrimitive` | `name :: inline primitive: (Fn ...)` | `add-i64 :: inline primitive: (Fn [Int Int] Int)` |
| 11 | Extern primitive | `ExternPrimitive` | `name :: extern primitive: (Fn ...)` | `int-to-string :: extern primitive: (Fn [Int] String)` |
| 12 | Constructor (nullary) | `Constructor` | `Type.name :: Type` | `Option.None :: (Option a)` |
| 13 | Constructor (data) | `Constructor` | `Type.name :: (Fn [...] Type)` | `Option.Some :: (Fn [a] (Option a))` |
| 14 | Constrained fn | `ConstrainedFn` | `name :: (Fn [:Trait a ...] ...)` | `add :: (Fn [:Num a a] a)` |
| 15 | Overloaded fn | `OverloadedFn` | `name :: sig1\n          sig2` | `map :: (Fn [... Vec] Vec)\n       (Fn [... List] List)` |
| 16 | Plain user fn | `UserFn` | `name :: (Fn [...] ...)` | `foo :: (Fn [a] a)` |

## Value Display

When an expression is not a recognized symbol, it is compiled and executed. The result is formatted as `value :: Type`:

| Type | Format | Example |
|------|--------|---------|
| `Int` | decimal integer | `42 :: Int` |
| `Bool` | `true` / `false` | `true :: Bool` |
| `Float` | decimal float | `3.14 :: Float` |
| `String` | quoted string | `"hello" :: String` |
| `Fn` | closure address | `<closure@0x1234> :: (Fn [a] a)` |
| `ADT` (nullary) | constructor name | `None :: (Option a)` |
| `ADT` (data) | `(Ctor fields...)` | `(Some 42) :: (Option Int)` |
| `Vec` | `[elem1 elem2]` | `[1 2 3] :: (Vec Int)` |
| `List` | `(list elem1 elem2)` | `(list 1 2 3) :: (List Int)` |
| `Seq` | `(seq elem1 elem2)` | `(seq 0 1 2 ... +more) :: (Seq Int)` |
| `IO` | underlying value | `0 :: IO Int` |

## REPL Slash Commands

| Command | Alias | Description |
|---------|-------|-------------|
| `/help` | `/h` | List all commands |
| `/sig <name>` | `/s` | Show signature with inferred types and docstring |
| `/doc <name>` | `/d` | Show docstring |
| `/type <expr>` | `/t` | Show type without evaluating |
| `/info <name>` | `/i` | Type, source, code size, compile time, specializations |
| `/source <name>` | — | Show original source text |
| `/clif <name>` | — | Show Cranelift IR |
| `/disasm <name>` | — | Show disassembled native code |
| `/time <expr>` | — | Evaluate with timing breakdown |
| `/list [name]` | `/l` | List in-scope symbols, optionally filtered; `/l <module>` lists module defs |
| `/mod [name]` | — | Switch namespace; no arg = user; loads module if needed |
| `/mem [<expr>]` | `/m` | Allocation stats, deltas for expr, `/mem reset` |
| `/quit` | `/q` | Exit the REPL |

### `/sig` — Signature Display

Reconstructs a source-like signature with inferred types as annotations:

```
> /sig inc
(defn inc "Increment by one" [:Int x] Int)

> /sig reduce
(defn reduce "Reduce collection to single value..."
  ([:(Fn [a b] a) f :a init :(Vec b) v] a)
  ([:(Fn [a b] a) f :a init :(List b) l] a)
  ([:(Fn [a b] a) f :a init :(Seq b) s] a))

> /sig Display
(deftrait Display "Convert to string representation"
  (show "Convert value to string" [self] String)) | impl Int, Float, Bool, String

> /sig Option
(deftype (Option a) "An optional value, either None or Some"
  (None "Represents absence of a value")
  (Some "Wraps a present value" [:a val]))
```

### `/doc` — Docstring Lookup

Searches for docstrings in this order: `symbol_meta` (functions, primitives, special forms), trait declarations, trait methods, type definitions, constructors, macros.

## Docstrings

Optional string literals in definition forms, used by `/sig` and `/doc`:

```clojure
(defn name "docstring" [params...] body)
(defn name "docstring" ([params1...] body1) ([params2...] body2))
(deftrait Name "docstring" (method "docstring" [params...] RetType))
(deftype Name "docstring" (Ctor "docstring" [:Type field]) ...)
```

Metadata is stored in `ModuleEntry::Def.meta` (`SymbolMeta` enum: `SpecialForm`, `Primitive`, `UserFn`) for functions and special forms, and in `TypeDefInfo.docstring` / `ConstructorInfo.docstring` for types. `SpecialForm` and `Primitive` variants require `String` docstrings (not `Option`) — the Rust compiler enforces documentation for all built-in symbols. Reads use `get_symbol_meta()` which delegates to `resolve_symbol_meta_via_modules()`.

## Implementation

- `src/repl/format.rs` — `special_form_description()`, `special_form_docstring()`, `format_symbol_info()`, `format_fn_sig()`, `format_trait_sig()`, `format_type_def_sig()`, `format_type_as_annotation()`, `format_result_value()`, `format_type_for_display()`, `format_scheme_for_display()`
- `src/repl/input.rs` — `handle_expr()` implements the decision tree
- `src/repl/handlers.rs` — `/type`, `/info`, `/sig`, `/doc` commands
- `src/typechecker/introspect.rs` — `describe_symbol()` classification, `list_symbols()` iterates scope for in-scope names
- `src/typechecker/mod.rs` — `SymbolInfo` enum, `SymbolMeta` enum, `PrimitiveKind` enum, `TypeDefInfo`, `ConstructorInfo`
- `src/display.rs` — `format_trait_decl()`, `format_trait_method_type()`, `format_trait_method_type_with_params()`, `format_type_def()`
