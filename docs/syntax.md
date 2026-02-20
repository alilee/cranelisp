# Syntax

## S-Expression Grammar

Cranelisp uses S-expression syntax with Clojure-style conventions.

### Atoms

```clojure
42          ; integer literal (i64)
-7          ; negative integer
3.14        ; float literal (f64)
-0.5        ; negative float
true        ; boolean literal
false       ; boolean literal
"hello"     ; string literal
foo         ; symbol (variable reference)
my-func     ; symbols may contain hyphens
```

Symbols start with a letter or underscore, followed by letters, digits, underscores, or hyphens.

### Arithmetic and Comparison Operators

All operators are prefix, written as function calls. They are trait methods dispatched at compile time:

```clojure
(+ 1 2)     ; addition (Num trait)
(- 10 3)    ; subtraction
(* 4 5)     ; multiplication
(/ 10 2)    ; division

(= a b)     ; equality (Eq trait)
(< a b)     ; less than (Ord trait)
(> a b)     ; greater than
(<= a b)    ; less or equal
(>= a b)    ; greater or equal
```

Arithmetic operators work on both `Int` and `Float` via the `Num` trait. Comparisons return `Bool`.

### Special Forms

#### `defn` — Function Definition

```clojure
(defn name [param1 param2 ...]
  body)
```

Parameters are listed in square brackets (Clojure-style). The body is a single expression.

Parameters may have type annotations using the `:Type name` syntax:

```clojure
(defn f [:Int x :Bool y] ...)         ; concrete type annotations
(defn add [:Num x :Num y] (+ x y))   ; trait constraint annotations
```

Concrete annotations (`:Int`, `:String`, `:(Option Int)`) constrain the parameter to that type. Trait annotations (`:Num`, `:Display`) add a trait constraint to the parameter's type variable, producing a constrained polymorphic function. See `docs/constrained-polymorphism.md`.

An optional docstring (string literal) may appear between the name and the parameters:

```clojure
(defn inc "Increment by one" [:Int x] (+ x 1))
```

Multi-signature variant (see `docs/multi-sig.md`):

```clojure
(defn name "optional docstring"
  ([params1...] body1)
  ([params2...] body2)
  ...)
```

#### `let` — Local Bindings

```clojure
(let [x 1 y 2]
  (+ x y))
```

Bindings are pairs in square brackets. The body sees all bindings. Bindings are evaluated left to right.

#### `if` — Conditional

```clojure
(if condition
  then-expr
  else-expr)
```

Both branches are required. The condition must be `Bool`.

#### `fn` — Lambda (Anonymous Function)

```clojure
(fn [param1 param2 ...] body)
```

Creates an anonymous function value. Can be called immediately, bound with `let`, or passed as an argument. Lambdas capture variables from their enclosing scope (closures). See `docs/closures.md`. Lambda parameters support the same `:Type name` annotations as `defn`.

```clojure
((fn [x] (+ x 1)) 5)                       ; → 6
(let [f (fn [x] (* x 2))] (f 10))          ; → 20
(defn make-adder [n] (fn [x] (+ n x)))     ; closure capturing n
```

#### `do` — Expression Sequencing (macro)

```clojure
(do expr1 expr2 ... exprN)
```

A prelude macro that expands to nested `let` bindings. Evaluates expressions left to right. Returns the value of the last expression. Used for sequencing effects.

```clojure
(defn main []
  (do
    (print (show 42))
    (print (show 100))))

;; expands to:
(defn main []
  (let [_ (print (show 42))]
    (print (show 100))))
```

#### `pure` — Lift to IO (function)

```clojure
(pure expr)
```

A library function that wraps a value in an `IOVal` constructor, producing an `IO a`. Required when mixing pure and effectful branches in `if`.

```clojure
(if (> x 0)
  (print (show x))   ; IO Int
  (pure 0))          ; IO Int
```

#### `bind` — Monadic Extraction (function)

```clojure
(bind io-expr continuation)
```

A library function that pattern-matches `IOVal` to extract the inner value from `IO a`, then passes it to a continuation `a -> IO b`.

```clojure
(bind (print (show 42))
  (fn [result] (pure (+ result 1))))
```

#### `bind!` — Monadic Bind Sugar (macro)

```clojure
(bind! [name io-expr]
  body)
```

A prelude macro that desugars to nested `bind`/`fn` calls, avoiding deeply nested continuations.

Multiple bindings are supported — they desugar to nested `bind`/`fn` chains:

```clojure
(bind! [line (read-line)
       result (pure (parse-int line))]
  (match result
    [(Some n) (pure n)
     None (pure 0)]))

;; desugars to:
(bind (read-line) (fn [line]
  (bind (pure (parse-int line)) (fn [result]
    (match result
      [(Some n) (pure n)
       None (pure 0)])))))
```

#### `deftrait` — Trait Declaration

```clojure
(deftrait TraitName "optional docstring"
  (method1 "optional docstring" [Self] ReturnType)
  (method2 "optional docstring" [Self OtherType] ReturnType))
```

Higher-kinded traits use type constructor parameters (lowercase):

```clojure
(deftrait (Functor f) "Mappable container"
  (fmap "Apply function to values inside container" [(Fn [a] b) (f a)] (f b)))
```

Declares a trait with method signatures. Optional docstrings on both the trait and individual methods. See `docs/traits.md` and `docs/hkt.md`.

#### `impl` — Trait Implementation

```clojure
(impl TraitName TargetType
  (defn method1 [x] body1)
  (defn method2 [x y] body2))
```

For HKT traits, the target is a bare type constructor name:

```clojure
(impl Functor Option
  (defn fmap [f opt] ...))
```

Provides method bodies for a specific type. See `docs/traits.md`.

### Function Application

```clojure
(callee arg1 arg2 ...)
```

The callee can be any expression — a symbol, a lambda, or any expression that evaluates to a function.

```clojure
(fact 10)                     ; call named function
((fn [x] (* x x)) 7)         ; call lambda directly
(let [f double] (f 5))        ; call via variable
```

### Type Annotations

The `:Type expr` syntax annotates an expression with a type:

```clojure
:Int 42                    ; constrain 42 to Int
:(Option Int) None         ; constrain None to (Option Int)
:(Fn [Int] Bool) f         ; constrain f to (Fn [Int] Bool)
```

The annotation is checked at compile time — the expression's inferred type must be compatible with the annotation. Concrete types (`:Int`, `:(Option Int)`) are unified with the expression's type. This is useful for disambiguating polymorphic constructors like `None`.

The same `:Type name` syntax is used in parameter lists (see `defn` and `fn` above) and in `deftype` field definitions (see `docs/adt.md`).

### `defmacro` — Macro Definition

```clojure
(defmacro name [params] body)
(defmacro name [params & rest] body)
```

Defines a compile-time macro. The macro body receives its arguments as `(SList Sexp)` and returns a `Sexp` that replaces the macro call. The `Sexp` and `SList` types live in the synthetic `macros` module (compiler-seeded, not user-modifiable). Macros run before type checking.

Use quasiquote (`` ` ``) with unquote (`~`) and unquote-splicing (`~@`) to build output forms readably:

```clojure
(defmacro my-inc [x]
  `(+ ~x 1))

(my-inc 41)  ; expands to (+ 41 1) → 42
```

```clojure
(defmacro when [c b]
  `(if ~c ~b 0))

(defmacro my-let1 [v e b]
  `(let [~v ~e] ~b))
```

Use `~@` to splice a list of expressions into the output:

```clojure
(defmacro my-add [& args]
  `(+ ~@args))

(my-add 40 2)  ; expands to (+ 40 2) → 42
```

Use `&` before the last parameter to capture remaining arguments as an SList:

```clojure
(defmacro first-of [& args] (shead args))
```

Manual Sexp constructor calls also work (quasiquote desugars to these). Use `slist` to build `(SList Sexp)` values for `SexpList`/`SexpBracket` fields:

```clojure
(defmacro my-inc [x]
  (SexpList (slist (SexpSym "+") x (SexpInt 1))))
```

Macro bodies must return a value of type `Sexp`. A macro whose body returns a different type (e.g. `Int`, `Float`) is a compile-time error:

```clojure
(defmacro bad [] 3.14)  ; ERROR: macro 'bad' body has type Float, expected Sexp
```

#### Bare-symbol expansion

Zero-arg macros expand when referenced as bare symbols (without parentheses):

```clojure
(defmacro always-one [] (SexpInt 1))
always-one  ; → 1 (no parens needed)
```

#### `begin` — Multi-form expansion

A macro can return `(begin form1 form2 ...)` to splice multiple top-level forms. `begin` is handled during macro expansion and is not valid in user source code:

```clojure
(defmacro my-pair [name a b]
  `(begin
    (defn ~(make-def-name name) [] ~a)
    (defn ~name [] ~b)))
```

### `const` — Named Constant

```clojure
(const name value)
(const- name value)     ; private
```

Defines a compile-time constant. The value is substituted inline wherever the name appears (via zero-arg macro expansion):

```clojure
(const PI 3.14)
(const ANSWER 42)
(const GREETING "hello")

(* PI 2.0)    ; → (* 3.14 2.0)
```

`const-` creates a module-private constant.

### `def` — Named Value

```clojure
(def name value)
(def- name value)       ; private
```

Defines a named value. Unlike `const`, the value expression is evaluated once (as a zero-arg function) and called by reference:

```clojure
(def ten (+ 5 5))       ; creates ten-def function, ten macro calls it
(def pi 3.14)

(show ten)              ; → "10"
```

`def-` creates a module-private value.

### `str-concat` — String Concatenation

```clojure
(str-concat "hello" " world")  ; → "hello world"
```

Concatenates two strings. Available as a primitive function.

### `quote-sexp` — Quote Sexp Values

```clojure
(quote-sexp (SexpInt 42))  ; → (SexpList (SCons (SexpSym "SexpInt") (SCons (SexpInt 42) SNil)))
```

Converts a runtime `Sexp` value into constructor source code — a new `Sexp` that, when evaluated, reconstructs the original. Used internally by `const` and `def` macros.

See `docs/macros.md` for the full macro system design.

### Comments

Line comments start with `;`:

```clojure
; this is a comment
(+ 1 2) ; inline comment
```

### REPL Save-to-File

The REPL acts as a live editor — every successful definition (`defn`, `deftype`, `deftrait`, `impl`, `import`, `defmacro`, `mod`) automatically regenerates the backing `.cl` source file for the current module. For a bare REPL (no entry file), definitions are saved to `user.cl` in the current working directory.

`(mod foo)` declares a child module. If `foo.cl` exists as a sibling of the current module's file, it is loaded; otherwise an empty `foo.cl` is created. The declaration is persisted to the parent module's file. Note that `(mod foo)` does not switch into the child module — use `/mod foo` to switch.

The generated file uses a consistent section ordering:

1. Module declarations (`(mod ...)`)
2. Imports (merged into a single `(import [...])`)
3. Exports (merged into a single `(export [...])`)
4. Trait declarations
5. Type definitions
6. Trait implementations
7. Functions and macros (dependency-sorted)

Constructor and trait method references in expression bodies are qualified with dot notation (e.g. `Option.Some`, `Display.show`, `Num.+`) for unambiguous round-tripping.

### Platform Declaration

```clojure
(platform "stdio")     ; declare use of the built-in stdio platform
```

The `(platform "name")` form declares which platform a module uses. It is only valid at the top level of a source file, alongside `(mod ...)`, `(import ...)`, and `(export ...)`. The argument must be a string literal.

- When absent, the built-in stdio platform is used (backward compatible)
- `(platform "stdio")` is explicitly allowed and equivalent to the default
- Multiple `(platform ...)` forms are allowed in the same file (for future multi-platform support)
- Only the entry module's platform declarations are checked
- Non-"stdio" platform names are resolved via `resolve_platform_path` (DLL loading, not yet wired)

### Program Structure

A program is a sequence of top-level forms: `defn`, `deftrait`, and `impl`. Execution starts at `main`, which must return `IO _`:

```clojure
(defn helper [x]
  (* x x))

(defn main []
  (print (show (helper 6))))
```

### Builtins

- `print` — prints a string followed by a newline, returns 0. Type: `String -> IO Int`.
- `read-line` — reads a line from stdin (trimming trailing newline). Type: `(fn [] (IO String))`.
- `parse-int` — parses a string as an integer, returning `None` on failure. Type: `String -> (Option Int)`. Pure function (no IO).
- `show` — converts a value to its string representation. Type: `Display a => a -> String`. Implementations for Int, Bool, String, Float.
- `fmap` — maps a function over a container. Type: `Functor f => (a -> b) -> f a -> f b`. Implementations for Option, List. See `docs/hkt.md`.

#### Vec Operations

- `vec-get` — index into a Vec (bounds-checked). Type: `(fn [(Vec a) Int] a)`.
- `vec-set` — return new Vec with element at index replaced. Type: `(fn [(Vec a) Int a] (Vec a))`.
- `vec-push` — return new Vec with element appended. Type: `(fn [(Vec a) a] (Vec a))`.
- `vec-len` — return the length of a Vec. Type: `(fn [(Vec a)] Int)`.

#### List Operations

- `empty?` — test if a List is Nil. Type: `(fn [(List a)] Bool)`.
- `concat` — concatenate two lists. Type: `(fn [(List a) (List a)] (List a))`.
- `head` — first element (auto-generated field accessor). Type: `(fn [(List a)] a)`.
- `tail` — rest of the list (auto-generated field accessor). Type: `(fn [(List a)] (List a))`.
- `list-map` — map a function over a List. Type: `(fn [(fn [a] b) (List a)] (List b))`.
- `list-reduce` — left fold over a List. Type: `(fn [(fn [b a] b) b (List a)] b)`.

#### Unified Collection API (Multi-sig)

These functions dispatch on the container type (Vec, List, or Seq) using multi-sig dispatch. `map`, `filter`, `take`, and `drop` return lazy Seq values. `reduce` is eager.

- `map` — lazy map over any collection. Type: `(fn [(fn [a] b) C] (Seq b))` where `C` is Vec, List, or Seq.
- `filter` — lazy filter over any collection. Type: `(fn [(fn [a] Bool) C] (Seq a))` where `C` is Vec, List, or Seq.
- `take` — lazy take first N elements. Type: `(fn [Int C] (Seq a))` where `C` is Vec, List, or Seq.
- `drop` — lazy drop first N elements. Type: `(fn [Int C] (Seq a))` where `C` is Vec, List, or Seq.
- `reduce` — eager left fold over any collection. Type: `(fn [(fn [b a] b) b C] b)` where `C` is Vec, List, or Seq.
- `seq` — convert a Vec or List to a lazy Seq. Type: `(fn [C] (Seq a))` where `C` is Vec or List.

#### Lazy Sequence Operations

- `to-list` — materialize a Seq to a List (eager — does not terminate on infinite Seq). Type: `(fn [(Seq a)] (List a))`.
- `range-from` — infinite sequence of integers starting at N. Type: `(fn [Int] (Seq Int))`.
- `iterate` — infinite sequence from repeated function application: `x, (f x), (f (f x)), ...`. Type: `(fn [(fn [a] a) a] (Seq a))`.
- `repeat` — infinite sequence of a single value. Type: `(fn [a] (Seq a))`.
- `inc` — increment an integer by 1. Type: `(fn [Int] Int)`.
