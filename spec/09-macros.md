# 9. Macros [R3 S9]

This section defines the compile-time macro system in Cranelisp. Macros are ordinary Cranelisp functions that transform S-expression values before type checking. They are compiled with the same code generation pipeline as user functions and called during expansion — no separate interpreter is required.

## 9.1 Sexp Data Model [R3 S9]

The macro system operates on S-expression values. Two algebraic data types are provided by the compiler in a synthetic `macros` module. These types are immutable and not user-modifiable.

### 9.1.1 SList Type

```clojure
(deftype (SList a)
  SNil
  (SCons [:a shead :(SList a) stail]))
```

`SList` is a singly linked list used to represent sequences of S-expressions. It is distinct from the user-visible `List` type to decouple the macro system from user-modifiable standard library code.

- `SNil` -- the empty list (nullary constructor, tag 0)
- `(SCons shead stail)` -- a cons cell with head element and tail list

### 9.1.2 Sexp Type

```clojure
(deftype Sexp
  (SexpInt [:Int sval])
  (SexpFloat [:Float sval])
  (SexpBool [:Bool sval])
  (SexpStr [:String sval])
  (SexpSym [:String sname])
  (SexpList [:(SList Sexp) sitems])
  (SexpBracket [:(SList Sexp) sitems]))
```

Each variant represents one kind of S-expression:

| Variant | Description | Example source |
|---|---|---|
| `SexpInt` | Integer literal | `42` |
| `SexpFloat` | Float literal | `3.14` |
| `SexpBool` | Boolean literal | `true` |
| `SexpStr` | String literal | `"hello"` |
| `SexpSym` | Symbol (identifiers, operators, keywords) | `foo`, `+`, `defn` |
| `SexpList` | Parenthesized list `(...)` | `(+ 1 2)` |
| `SexpBracket` | Bracketed list `[...]` | `[x y z]` |

Field names are prefixed with `s` (e.g., `sval`, `sname`, `sitems`) to avoid collision with user-defined field names.

### 9.1.3 Module Availability

Both `Sexp` and `SList` live in the synthetic `macros` module, which is compiler-seeded (like the `primitives` module). They are NOT automatically imported — modules that need bare access to Sexp constructors (e.g., for pattern matching on macro arguments) MUST include `(import [macros [*]])`. Qualified access (`macros/SexpSym`, etc.) is always available without import.

Simple quasiquote-based macros work without importing the macros module, because the expander emits qualified constructor references (`macros/SexpSym`, `macros/SCons`, etc.) internally. Only macros that directly reference Sexp constructors in their body (e.g., pattern matching on `SexpList`) require the explicit import.

### 9.1.4 Marshalling

At macro expansion time, the implementation MUST convert between its internal S-expression representation and the runtime `Sexp` ADT values:

- Before calling a macro function, the implementation converts each argument from internal form to a heap-allocated `Sexp` ADT value.
- After the macro function returns, the implementation converts the result from a runtime `Sexp` ADT value back to the internal form.

The heap layout of marshalled values follows the standard ADT representation defined in Section 12.1.4. The details of the marshalling functions are implementation-defined.

## 9.2 Macro Definition [R3 S9]

### 9.2.1 Syntax

```ebnf
defmacro_form  = '(' 'defmacro' name docstring? clause+ ')'
               | '(' 'defmacro-' name docstring? clause+ ')'

clause         = params body                    ;; single-clause shorthand
               | '(' params body ')'            ;; explicit clause

name           = symbol
docstring      = string
params         = '[' param* ('&' param)? ']'
param          = symbol | bracket_pattern
bracket_pattern = '[' symbol* ('&' symbol)? ']'
body           = expr
```

The `defmacro` form defines a named compile-time macro. The `defmacro-` variant defines a module-private macro.

```clojure
(defmacro name [params] body)
(defmacro name [params & rest] body)
(defmacro name "docstring" [params] body)
(defmacro- name [params] body)
```

### 9.2.2 Parameters

Each parameter receives a value of type `Sexp`. When the macro is invoked as `(name arg1 arg2 arg3)`, each argument S-expression is passed as a separate `Sexp` value to the corresponding parameter.

The `& rest` syntax captures all remaining arguments as a single value of type `(SList Sexp)`. The `&` MUST appear before exactly one parameter name in the parameter list, and that parameter MUST be the last.

```clojure
;; Fixed arity: two Sexp parameters
(defmacro my-if [cond body]
  `(if ~cond ~body 0))

;; Variadic: one Sexp parameter, rest captured as (SList Sexp)
(defmacro my-add [& args]
  `(+ ~@args))

;; Mixed: one fixed Sexp, rest as (SList Sexp)
(defmacro -> [x & forms]
  (thread-first-fold x forms))
```

### 9.2.3 Return Type Constraint

The body of a macro MUST return a value of type `Sexp`. If the body has any other type, the implementation MUST report a compile-time error.

```clojure
;; Valid: body returns Sexp
(defmacro always-one [] (SexpInt 1))

;; INVALID: body returns Float — compile-time error
(defmacro bad [] 3.14)
;; Error: macro 'bad' body has type Float, expected Sexp
```

### 9.2.4 Docstrings

An optional string literal MAY appear between the macro name and the parameter list. This string serves as documentation and is accessible via REPL introspection commands.

```clojure
(defmacro list "Construct a list from elements" [& elems]
  (sfold (fn [acc e] `(Cons ~e ~acc)) `Nil (sreverse elems)))
```

### 9.2.5 Macro Body Capabilities

Macro bodies are full Cranelisp expressions. They MAY use:

- Pattern matching (`match`) on `Sexp` and `SList` values
- Lambda functions (`fn`)
- Local bindings (`let`)
- Calls to any function or macro defined before the current macro
- Recursive calls (including via helper functions)
- All `Sexp` and `SList` constructors

Macro bodies MUST NOT perform IO operations. They are pure functions from `Sexp` to `Sexp`.

### 9.2.6 Multi-Clause Macros

A `defmacro` form MAY contain multiple clauses. Each clause is a `([params] body)` pair enclosed in parentheses:

```clojure
(defmacro cond "Multi-way conditional with mandatory default"
  ([x] x)
  ([x body & rest] `(if ~x ~body (cond ~@rest))))
```

When a single `[params] body` pair is provided without enclosing parentheses, it is treated as a single-clause macro (the original syntax). Multi-clause and single-clause forms are interchangeable when there is only one clause.

At expansion time, clauses are tried in definition order — the first matching clause wins. A clause matches when:

1. The number of positional arguments matches the clause's fixed parameter count (or the clause has a rest parameter `&`).
2. Any bracket pattern parameters (see Section 9.2.7) match the corresponding argument's structure and element count.

If no clause matches, the implementation MUST report a compile-time error naming the macro and the argument count.

Each clause is compiled independently into a separate function. The dispatch occurs at expansion time, not at compile time of the macro definition.

```clojure
;; Recursive base/step pattern:
(defmacro list
  ([] `Nil)
  ([x & rest] `(Cons ~x (list ~@rest))))

;; Arity dispatch:
(defmacro str
  ([] (SexpStr ""))
  ([x] `(show ~x))
  ([x & rest] `(str-concat (show ~x) (str ~@rest))))

;; IO sequencing:
(defmacro do
  ([x] x)
  ([x & rest] `(let [_ ~x] (do ~@rest))))
```

### 9.2.7 Bracket Destructuring Parameters

A parameter in a macro clause MAY be a bracket pattern instead of a plain symbol. A bracket pattern matches an argument that is an `SexpBracket` (square-bracket form) and destructures its contents:

```clojure
;; [name expr] matches a bracket with exactly 2 elements
(defmacro my-let [[name expr] body]
  `(let [~name ~expr] ~body))

;; [a & rest] matches a bracket with 1+ elements
(defmacro first-of [[a & rest]]
  a)

;; [] matches an empty bracket
(defmacro empty? [[]]
  `true)
```

Bracket patterns support the same `&` rest syntax as top-level parameter lists. Without a rest parameter, the bracket MUST contain exactly the number of fixed names. With a rest parameter, it MUST contain at least the number of fixed names; remaining elements are collected into an `(SList Sexp)`.

If a call-site argument is not an `SexpBracket`, or if its element count does not match, the clause does not match (and the next clause is tried in a multi-clause macro, or an error is reported in a single-clause macro).

Bracket destructuring composes with multi-clause dispatch. The `derive` macro uses both:

```clojure
(defmacro derive [& traits] dt]
  ...)  ; traits is a bracket pattern, dt is a plain Sexp
```

## 9.3 Macro Expansion [R3 S9]

### 9.3.1 Pipeline Position

Macro expansion occurs after S-expression parsing and before AST construction and type checking:

```
Source text
  --> [S-expression parser] --> Sexp tree
  --> [Macro expander]      --> Expanded Sexp tree
  --> [AST builder]         --> AST
  --> [Type checker]        --> [Code generator] --> Executable
```

### 9.3.2 Expansion Process

When the expander encounters a list form `(name arg1 arg2 ...)` where `name` is a registered macro:

1. For multi-clause macros, each clause is tested in definition order: the argument count and any bracket pattern constraints are checked against the call-site arguments. The first matching clause is selected. If no clause matches, a compile-time error is reported.
2. Each argument `arg1`, `arg2`, ... is marshalled from the internal S-expression representation to a runtime `Sexp` ADT value.
3. For variadic macros (clauses with `&` rest), the arguments beyond the fixed parameters are collected into an `(SList Sexp)` value. For bracket pattern parameters, the argument's bracket contents are destructured into individual bindings.
4. The compiled macro function for the selected clause is called with the marshalled arguments.
5. The return value (a runtime `Sexp` ADT) is marshalled back to the internal S-expression representation.
6. The result replaces the original macro call form.
7. The result is re-expanded (see Section 9.3.3).

### 9.3.3 Re-expansion and Fixed Point

After a macro produces its expansion, the result MUST be re-expanded. This allows macros to expand into calls to other macros. Expansion continues until the result contains no more macro calls (a fixed point is reached).

Implementations SHOULD limit the number of expansion iterations to prevent infinite loops. The recommended limit is 500 iterations. If the limit is exceeded, the implementation MUST report a compile-time error.

```clojure
;; Macro expanding to another macro call:
(defmacro double-list [a b]
  `(list ~a ~a ~b ~b))

(double-list 1 2)
;; First expansion:  (list 1 1 2 2)
;; Second expansion: (Cons 1 (Cons 1 (Cons 2 (Cons 2 Nil))))
;; Fixed point reached (no more macros)
```

### 9.3.4 Define-Before-Use

Macros MUST be defined before they are referenced. A macro call to a name that has not yet been defined as a macro is NOT expanded — it passes through to the AST builder as a regular function call.

Within a source file, top-level forms are processed sequentially. A `defmacro` form is compiled and registered immediately when encountered. All subsequent forms in the file may use that macro.

A `defmacro` body MAY reference any function or macro that was defined before it. Forward references to macros are NOT supported.

### 9.3.5 Span Attribution

The expanded S-expressions SHOULD carry the source location (span) of the original macro call site. This means that error messages resulting from expanded code point to where the macro was invoked, not where the macro was defined.

## 9.4 Quasiquote [R3 S9]

Quasiquote is reader syntax for template-based S-expression construction. It avoids the verbosity of manually calling `Sexp` constructors.

### 9.4.1 Syntax

| Syntax | Name | Meaning |
|---|---|---|
| `` `form `` | Quasiquote | Wrap `form` as `Sexp` constructor calls |
| `~expr` | Unquote | Evaluate `expr` (MUST produce `Sexp`) and splice result in |
| `~@expr` | Unquote-splicing | Evaluate `expr` (MUST produce `(SList Sexp)`) and splice each element |

Quasiquote is parsed at the S-expression level as syntactic sugar:

- `` `form `` parses as `(quasiquote form)`
- `~expr` parses as `(unquote expr)`
- `~@expr` parses as `(unquote-splicing expr)`

During expansion, quasiquote forms are desugared into explicit `Sexp` constructor calls using `SexpSym`, `SexpInt`, `SexpList`, `SCons`, `SNil`, etc.

### 9.4.2 Quasiquote Semantics

Within a quasiquoted form:

- **Literal atoms** (integers, floats, booleans, strings) are wrapped in their corresponding `Sexp` constructor. For example, `42` becomes `(SexpInt 42)`.
- **Symbols** become `SexpSym` calls. For example, `foo` becomes `(SexpSym "foo")`.
- **Lists** `(a b c)` become `(SexpList (SCons <a> (SCons <b> (SCons <c> SNil))))` where `<a>`, `<b>`, `<c>` are the recursively quasiquoted elements.
- **Brackets** `[a b c]` become `(SexpBracket (SCons <a> (SCons <b> (SCons <c> SNil))))`.
- **Unquote** `~expr` evaluates `expr` in the current scope. The result MUST be of type `Sexp` and is spliced into the template at that position.
- **Unquote-splicing** `~@expr` evaluates `expr` in the current scope. The result MUST be of type `(SList Sexp)`. Each element of the list is spliced into the surrounding list. Unquote-splicing MUST only appear inside a list or bracket form.

### 9.4.3 Examples

Building an `if` form with quasiquote versus manual constructors:

```clojure
;; With quasiquote:
(defmacro my-if [c t e]
  `(if ~c ~t ~e))

;; Equivalent without quasiquote:
(defmacro my-if [c t e]
  (SexpList (SCons (SexpSym "if") (SCons c (SCons t (SCons e SNil))))))
```

Using unquote-splicing to spread arguments:

```clojure
(defmacro my-add [& args]
  `(+ ~@args))

(my-add 1 2 3)
;; Expands to: (+ 1 2 3)
```

Nested quasiquote with symbol construction:

```clojure
(defmacro when [cond body]
  `(if ~cond ~body 0))

(when (> x 0) (print "positive"))
;; Expands to: (if (> x 0) (print "positive") 0)
```

## 9.5 Bare-Symbol Expansion [R3 S9]

Zero-argument macros expand when referenced as bare symbols, without parentheses. This enables named constants and value aliases.

Macro bodies must explicitly construct `Sexp` values — literals are not automatically lifted. Writing `(defmacro PI [] 3.14159)` is a compile-time error because the body has type `Float`, not `Sexp`. The `const` macro (Section 9.10.1) provides a more ergonomic way to define named constants that substitute literal values inline.

```clojure
(defmacro PI [] (SexpFloat 3.14159))
PI         ; expands to 3.14159 (no parentheses needed)
(* PI 2.0) ; expands to (* 3.14159 2.0)

(defmacro always-one [] (SexpInt 1))
always-one ; -> 1
```

An implementation MUST check for zero-argument macros during expansion whenever a bare symbol is encountered.

This mechanism can be used to implement named constants. For example, the reference implementation provides `const` and `def` macros (Section 9.10.1, 9.10.2) built on bare-symbol expansion.

## 9.6 Multi-Form Expansion (`begin`) [R3 S9]

A macro MAY return a form whose head symbol is `begin`. The `begin` form causes the expander to splice multiple top-level forms into the surrounding context:

```clojure
(begin form1 form2 ... formN)
```

Each `form1` through `formN` is treated as a separate top-level form, as if the macro call had been replaced by all of them in sequence.

`begin` is handled exclusively by the macro expander. It is NOT a valid user-level special form and MUST NOT appear in user source code outside of macro output. An implementation SHOULD report an error if `begin` appears in non-macro-expanded code.

**Example:**

```clojure
(defmacro def [name value]
  `(begin
    (defn ~(make-def-name name) [] ~value)
    (defmacro ~name [] (SexpList (SCons ~(quote-sexp (make-def-name name)) SNil)))))

(def ten (+ 5 5))
;; Expands to two top-level forms:
;;   (defn ten-def [] (+ 5 5))
;;   (defmacro ten [] (SexpList (SCons (SexpSym "ten-def") SNil)))
```

The `begin` expansion is performed before re-expansion of individual forms. Each spliced form is then expanded independently.

## 9.7 SList Helper Functions [R3 S9]

Macro authors typically need helper functions for `SList`. A standard library may provide functions such as the following (these are defined in the reference implementation's `core.syntax` module).

### 9.7.0 Visibility

The SList helper functions (`sfold`, `sreverse`, `sconcat`, `sempty?`) are public within `core.syntax` but only `sconcat` is re-exported through the prelude. This is because `sconcat` is used in code generated by the `~@` (unquote-splicing) quasiquote operator. The other helpers are available to sibling modules (such as `core.derive`) via direct import but are not part of the user-facing standard library namespace. Macro authors who need these helpers in their own modules can import them explicitly from `core.syntax` or define local equivalents.

### 9.7.1 `sfold`

```clojure
sfold :: (fn [b a b] b) -> b -> (SList a) -> b
```

Left fold over an SList. Applies the function to the accumulator and each element, left to right.

```clojure
(sfold (fn [acc x] (+ acc x)) 0 (SCons 1 (SCons 2 (SCons 3 SNil))))
;; -> 6
```

### 9.7.2 `sreverse`

```clojure
sreverse :: (fn [(SList a)] (SList a))
```

Reverse an SList.

```clojure
(sreverse (SCons 1 (SCons 2 (SCons 3 SNil))))
;; -> (SCons 3 (SCons 2 (SCons 1 SNil)))
```

### 9.7.3 `sconcat`

```clojure
sconcat :: (fn [(SList a) (SList a)] (SList a))
```

Concatenate two SLists. All elements of the first list appear before all elements of the second.

```clojure
(sconcat (SCons 1 (SCons 2 SNil)) (SCons 3 (SCons 4 SNil)))
;; -> (SCons 1 (SCons 2 (SCons 3 (SCons 4 SNil))))
```

### 9.7.4 `sempty?`

```clojure
sempty? :: (fn [(SList a)] Bool)
```

Test whether an SList is empty (`SNil`). Returns `true` for `SNil`, `false` for any `SCons`.

```clojure
(sempty? SNil)                   ; -> true
(sempty? (SCons 1 SNil))         ; -> false
```

### 9.7.5 `slist` Macro

```clojure
(slist e1 e2 ... eN)
```

A convenience macro that constructs an `(SList a)` from its arguments. Expands to nested `SCons`/`SNil` calls.

```clojure
(slist 1 2 3)
;; Expands to: (SCons 1 (SCons 2 (SCons 3 SNil)))
```

### 9.7.6 `shead` / `stail`

The field accessors `shead` and `stail` are auto-generated from the `SCons` constructor definition (as with all ADT field accessors). They extract the head element and tail list from a non-empty SList.

```clojure
(shead (SCons 1 (SCons 2 SNil)))   ; -> 1
(stail (SCons 1 (SCons 2 SNil)))   ; -> (SCons 2 SNil)
```

Calling `shead` or `stail` on `SNil` is a runtime error (match failure).

## 9.8 Hygiene [R3 S9]

Cranelisp macros are **unhygienic** by default. Names introduced by macro expansion are subject to capture by the expansion context, and names from the expansion context are visible inside macro-generated code.

### 9.8.1 Auto-Gensym

Symbols ending in `#` inside quasiquote templates are **auto-gensym** symbols. Within a single quasiquote expansion, all occurrences of the same `x#` produce the same unique generated name. Different quasiquote expansions produce different names, preventing accidental variable capture.

```clojure
;; Safe: x# generates a unique name each expansion
(defmacro my-let [v body] `(let [x# ~v] ~body))

(let [x 100]
  (my-let 42 (+ x 1)))
;; x# expands to a unique name like x__auto_1000042,
;; so the outer 'x' binding (100) is not captured.
;; Result: 101
```

### 9.8.2 Manual Strategies

For cases where auto-gensym is not sufficient, macro authors MAY also use:

- Naming conventions (e.g., prefixing introduced bindings with `__`)
- Using fixed internal names unlikely to conflict (e.g., `__case__` in the `case` macro)

```clojure
;; The 'case' macro uses a fixed internal name:
(defmacro case [expr & clauses]
  (SexpList (SCons (SexpSym "let")
    (SCons (SexpBracket (SCons (SexpSym "__case__") (SCons expr SNil)))
      (SCons (case-fold "__case__" clauses) SNil)))))
```

## 9.9 Macro Errors [R3 S9]

### 9.9.1 Return Type Mismatch

If a macro body's inferred type is not `Sexp`, the implementation MUST report a compile-time error at the `defmacro` form.

```clojure
(defmacro bad [] 42)
;; Error: macro 'bad' body has type Int, expected Sexp
```

### 9.9.2 Expansion Limit Exceeded

If macro expansion does not reach a fixed point within the implementation's iteration limit, the implementation MUST report a compile-time error indicating that expansion diverged.

### 9.9.3 Type Error in Macro Body

Macro bodies are type-checked like any other function. Type errors in the body (e.g., applying `shead` to an `Int`) are compile-time errors reported at the `defmacro` form.

```clojure
(defmacro bad [x]
  (shead x))
;; Error: shead expects (SList a), got Sexp
```

### 9.9.4 Runtime Error During Expansion

If a macro function raises a runtime error during expansion (e.g., pattern match failure on an unexpected `Sexp` variant), the implementation MUST report this as a compile-time error at the macro call site.

```clojure
(defmacro extract-int [x]
  (match x [(SexpInt n) (SexpInt n)]))

(extract-int "hello")
;; Error at call site: macro 'extract-int' failed during expansion
;; (match failure — "hello" is SexpStr, not SexpInt)
```

### 9.9.5 Arity Mismatch

Calling a macro with the wrong number of arguments is a compile-time error. For non-variadic macros, the number of arguments MUST exactly match the number of parameters. For variadic macros, the number of arguments MUST be at least the number of fixed parameters.

## 9.10 Example Prelude Macros [R3 S9]

The following macros illustrate the capabilities of the macro system. They are provided by the reference implementation's standard prelude (`lib/core/syntax.cl`) and are available in all modules that import the prelude (which is the default). Full details of the reference standard library are in Section 11 (non-normative); brief descriptions and expansion examples are given here.

### 9.10.1 `const` / `const-`

```clojure
(const name value)
(const- name value)
```

Defines a named compile-time constant. The value S-expression is captured and substituted inline wherever the name appears. This works by defining a zero-argument macro that returns the quoted value (Section 9.5).

```clojure
(const PI 3.14159)
(const GREETING "hello")

(* PI 2.0)    ; expands to (* 3.14159 2.0)
GREETING      ; expands to "hello"
```

`const-` creates a module-private constant.

**Implementation:**

```clojure
(defmacro const "Define a named constant (bare symbol expansion)" [name value]
  `(defmacro ~name [] ~(quote-sexp value)))
```

`const` uses the `quote-sexp` primitive (Section 9.11.1) to capture the value S-expression as a quoted form that reproduces the original value when evaluated.

### 9.10.2 `def` / `def-`

```clojure
(def name value)
(def- name value)
```

Defines a named value. Unlike `const`, the value expression is evaluated at runtime (as a zero-argument function). The name is defined as a macro that expands to a call to that function.

```clojure
(def ten (+ 5 5))

(show ten)    ; ten expands to (ten-def), which returns 10
```

`def-` creates a module-private value.

**Implementation:**

```clojure
(defmacro def "Define a named value (zero-arg function, bare symbol)" [name value]
  `(begin
    (defn ~(make-def-name name) [] ~value)
    (defmacro ~name [] (SexpList (SCons ~(quote-sexp (make-def-name name)) SNil)))))
```

This uses `begin` (Section 9.6) to emit two forms: a `defn` for the backing function and a `defmacro` for the bare-symbol expansion.

### 9.10.3 `list`

```clojure
(list e1 e2 ... eN)
```

Constructs a `List` value from its arguments. Expands to nested `Cons`/`Nil` constructor calls.

```clojure
(list 1 2 3)
;; Expands to: (Cons 1 (Cons 2 (Cons 3 Nil)))
```

**Implementation:**

```clojure
(defmacro list "Construct a list from elements" [& elems]
  (sfold (fn [acc e] `(Cons ~e ~acc)) `Nil (sreverse elems)))
```

Note: `list` builds user-visible `List` values (using `Cons`/`Nil`), while `slist` builds `SList` values (using `SCons`/`SNil`) for macro internals.

### 9.10.4 `do`

```clojure
(do e1 e2 ... eN)
```

Expression sequencing. Evaluates expressions left to right and returns the value of the last. Expands to nested `let` bindings with `_` as the binding name.

```clojure
(do (print "a") (print "b") (print "c"))
;; Expands to:
;; (let [_ (print "a")]
;;   (let [_ (print "b")]
;;     (print "c")))
```

**Implementation:**

```clojure
(defmacro do "Sequence expressions, return last value" [& body]
  (do-build body))
```

### 9.10.5 `bind!`

```clojure
(bind! [name1 io-expr1
        name2 io-expr2
        ...]
  body)
```

Monadic bind sugar. Desugars to nested `bind`/`fn` chains, avoiding deeply indented continuations.

```clojure
(bind! [line (read-line)
        n    (pure (parse-int line))]
  (print (show n)))

;; Expands to:
;; (bind (read-line) (fn [line]
;;   (bind (pure (parse-int line)) (fn [n]
;;     (print (show n))))))
```

The bindings argument MUST be a bracket form containing alternating name-expression pairs.

**Implementation:**

```clojure
(defmacro bind! "Monadic bind sugar" [bindings body]
  (let [items (match bindings [(SexpBracket xs) xs])]
    (bind!-fold items body)))
```

### 9.10.6 `->` (Thread-First)

```clojure
(-> initial form1 form2 ... formN)
```

Threads the initial value through a sequence of forms. Each form receives the accumulated result as its **first** argument. If a form is a list, the value is inserted after the function name. If a form is a bare symbol, it is called with the value as its sole argument.

```clojure
(-> 5 inc (* 2))
;; Step 1: (inc 5)
;; Step 2: (* (inc 5) 2)
;; Expands to: (* (inc 5) 2)

(-> "hello" (str-concat " ") (str-concat "world"))
;; Expands to: (str-concat (str-concat "hello" " ") "world")
```

**Implementation:**

```clojure
(defmacro -> "Thread value through forms as first argument" [x & forms]
  (thread-first-fold x forms))
```

### 9.10.7 `->>` (Thread-Last)

```clojure
(->> initial form1 form2 ... formN)
```

Threads the initial value through a sequence of forms. Each form receives the accumulated result as its **last** argument.

```clojure
(->> (list 1 2 3) (map inc) (reduce + 0))
;; Step 1: (map inc (list 1 2 3))
;; Step 2: (reduce + 0 (map inc (list 1 2 3)))
;; Expands to: (reduce + 0 (map inc (list 1 2 3)))
```

**Implementation:**

```clojure
(defmacro ->> "Thread value through forms as last argument" [x & forms]
  (thread-last-fold x forms))
```

### 9.10.8 `cond`

```clojure
(cond test1 body1
      test2 body2
      ...
      default)
```

Multi-way conditional. Tests are evaluated top to bottom; the body of the first true test is returned. The last form is the mandatory default (returned if no test is true).

```clojure
(cond (< x 0) "negative"
      (= x 0) "zero"
      "positive")

;; Expands to:
;; (if (< x 0) "negative"
;;   (if (= x 0) "zero"
;;     "positive"))
```

The argument list MUST have an odd number of forms: zero or more test-body pairs followed by a single default expression.

**Implementation:**

```clojure
(defmacro cond "Multi-way conditional with mandatory default" [& clauses]
  (cond-fold clauses))
```

### 9.10.9 `case`

```clojure
(case expr
  val1 body1
  val2 body2
  ...
  default)
```

Value dispatch using equality. The expression is evaluated once, then compared against each value. The body of the first matching value is returned. The last form is the mandatory default.

```clojure
(case color
  "red" 1
  "green" 2
  "blue" 3
  0)

;; Expands to:
;; (let [__case__ color]
;;   (if (= __case__ "red") 1
;;     (if (= __case__ "green") 2
;;       (if (= __case__ "blue") 3
;;         0))))
```

The expression is bound to an internal variable (`__case__`) to avoid multiple evaluation. The argument list MUST have an odd number of forms after the expression: zero or more value-body pairs followed by a default.

**Implementation:**

```clojure
(defmacro case "Dispatch on value equality with mandatory default" [expr & clauses]
  (SexpList (SCons (SexpSym "let")
    (SCons (SexpBracket (SCons (SexpSym "__case__") (SCons expr SNil)))
      (SCons (case-fold "__case__" clauses) SNil)))))
```

### 9.10.10 `vec`

```clojure
(vec e1 e2 ... eN)
```

Constructs a `Vec` from its arguments. Expands to a bracket form `[e1 e2 ... eN]`, which the AST builder interprets as a vector literal.

```clojure
(vec 1 2 3)
;; Expands to: [1 2 3]
;; AST builder produces a Vec literal node
```

**Implementation:**

```clojure
(defmacro vec "Construct a vec from elements" [& elems]
  (SexpBracket elems))
```

### 9.10.11 `str`

```clojure
(str e1 e2 ... eN)
```

String concatenation via `show`. Each argument is converted to a string with `show`, then all strings are concatenated with `str-concat`.

```clojure
(str "x = " x ", y = " y)
;; Expands to:
;; (str-concat (str-concat (str-concat (show "x = ") (show x)) (show ", y = ")) (show y))
```

With zero arguments, returns the empty string `""`.

**Implementation:**

```clojure
(defmacro str "Concatenate string representations of all arguments" [& args]
  (match args
    [SNil (SexpStr "")
     (SCons x rest)
       (str-fold (SexpList (SCons (SexpSym "show") (SCons x SNil))) rest)]))
```

## 9.11 Primitives for Macro Authors [R3 S9]

### 9.11.1 `quote-sexp`

```clojure
quote-sexp :: (fn [Sexp] Sexp)
```

Converts a runtime `Sexp` value into a new `Sexp` that, when evaluated, reconstructs the original. This is used internally by `const` and `def` to capture values as self-reproducing S-expressions.

```clojure
(quote-sexp (SexpInt 42))
;; -> (SexpList (SCons (SexpSym "SexpInt") (SCons (SexpInt 42) SNil)))
;; i.e., source code that evaluates to (SexpInt 42)
```

### 9.11.2 `str-concat`

```clojure
str-concat :: (fn [String String] String)
```

Concatenates two strings. Available as a primitive and commonly used in macro helpers that build symbol names.

```clojure
(str-concat "foo" "-def")   ; -> "foo-def"
```

## 9.12 Bootstrapping Order [R3 S9]

The prelude is loaded in two passes to resolve the circular dependency between type definitions and macro definitions:

1. **Pass 1 -- Type registration**: All `deftype` forms are scanned, parsed to AST, and registered in the type checker. This makes constructors available for use in macro bodies.

2. **Pass 2 -- Sequential compilation**: Forms are processed in source order:
   - `deftype` forms are skipped (already registered in Pass 1).
   - `defmacro` forms are compiled (with expansion of any earlier macros in the body), then registered in the macro environment. The compiled macro is immediately available for subsequent forms.
   - All other forms are expanded through the macro environment, then built into AST, type-checked, and compiled.

This ordering ensures that:
- Macro bodies can reference all type constructors (from Pass 1).
- Macro bodies can call helper functions defined earlier in the file.
- Macro bodies can use earlier macros (e.g., `slist` inside a macro body).
- User code can use all macros defined above it.

A `defmacro` MAY appear at any point in a source file, interleaved with other definitions. It is available to all subsequent forms in the same file and to any module that imports it.

## 9.13 REPL Integration [R3 S9]

In a REPL session:

- `defmacro` at the REPL compiles and registers the macro immediately. All subsequent input is expanded through the updated macro environment.
- The `/expand` (or `/e`) REPL command shows the result of macro expansion without evaluating it, which is useful for debugging macros.
- Macros appear in REPL introspection commands (`/list`, `/info`, `/sig`, `/doc`) alongside functions and types.

```
user> (defmacro double [x] `(+ ~x ~x))
double :: macro: (fn [Sexp] Sexp)
user> /expand (double 21)
(+ 21 21)
user> (double 21)
42 :: Int
```

## 9.14 Limitations [R3 S9]

The following features are NOT supported by the macro system:

1. **No fully hygienic macros**: Auto-gensym (`x#`) prevents accidental capture in most cases, but macro-introduced names are still subject to capture for names that don't use the `#` suffix (see Section 9.8).
2. **No forward references**: Macros must be defined before use.
3. **No user-defined reader macros**: Reader-level extensions (`'`, `` ` ``, `~`, `~@`, `#(...)`) are hardcoded. User-extensible reader macros (`defreader`) are planned but not yet implemented.
4. **No compile-time type access**: Macro bodies cannot inspect or query the types of their arguments. Macros operate on syntactic structure only.
5. **Error span limitation**: Error messages from expanded code point to the macro call site, not to the specific location within the macro definition body that produced the problematic form.
