# Examples Plan — Learning Sequence Design

**Date**: 2026-03-04
**Skill**: `/examples`
**Sprint**: 0, Task 10

Survey of prototype examples, learning sequence design, and concrete Ring 0 example sketches.

## 1. Prototype Example Inventory

The sketch contains 21 example files (plus 3 multi-file project directories) covering language features in a feature-oriented (non-sequential) style.

| # | File | Concept | Features Used | Ring |
|---|------|---------|---------------|------|
| 1 | `hello.cl` | Hello World | `platform`, `import`, `defn`, `print`, `show` | 4 |
| 2 | `factorial.cl` | Recursion | `defn`, `if`, `=`, `*`, `-`, recursion | 0* |
| 3 | `float.cl` | Float arithmetic | `+`, `*` on Float literals, `do`, `print` | 0* |
| 4 | `strings.cl` | String output | `print` with string literals, `show`, `do` | 4 |
| 5 | `closure.cl` | Closures & HOF | `fn`, closure capture, higher-order functions | 1 |
| 6 | `curry.cl` | Multi-sig & curry | `defn` multi-sig, auto-currying, `add-i64` | 2 |
| 7 | `adt.cl` | Algebraic data types | `deftype` (product, sum, enum), `match`, `impl Display` | 1 (enum portion: 0) |
| 8 | `traits.cl` | Trait definition | `deftrait`, `impl`, method dispatch | 2 |
| 9 | `list.cl` | List type | `list` macro, `head`, `tail`, `empty?`, recursion | 1 |
| 10 | `vec.cl` | Vec operations | Vec literal `[...]`, `vec-len`, `vec-get`, `vec-push`, `vec-set` | 1 |
| 11 | `macro.cl` | Macros | `defmacro`, `SexpList`, `SexpSym`, `SexpInt`, `slist` | 3 |
| 12 | `mapfold.cl` | Map/fold | `vec-map`, `vec-reduce`, `fmap`, `list-reduce`, lambdas | 2 |
| 13 | `seq.cl` | Lazy sequences | `range-from`, `iterate`, `repeat`, `take`, `filter`, `reduce` | 2 |
| 14 | `derived.cl` | Derive macros | `derive [Eq Ord Display]`, `=`, `<`, `<=`, `show` on ADT | 3 |
| 15 | `threading.cl` | Threading macros | `->`, `->>`, `cond`, `case`, `vec` | 3 |
| 16 | `functor.cl` | Functor trait (HKT) | `fmap` over Option and List, higher-kinded dispatch | 2 |
| 17 | `parallel.cl` | Parallel evaluation | `par-let`, `bind!`, `pure`, lenient eval | 4 |
| 18 | `reader.cl` | Reader shortcuts | `'` (quote), auto-gensym `x#`, `#(...)` anonymous fn | 3 |
| 19 | `sum-input.cl` | Interactive IO | `read-line`, `parse-int`, `bind!`, `match`, IO loop | 4 |
| 20 | `dot_notation.cl` | Qualified constructors | `Option.Some`, `Option.None`, `Num.+`, `Display.show` | 2 |
| 21 | `test-demo.cl` | Inline test module | `mod test`, `assert-eq`, `check`, `run-tests` | 4 |
| 22 | `imports/` (multi-file) | Cross-file imports | `mod`, `import`, `deftype`, private `defn-` | 2 |
| 23 | `modules/` (multi-file) | Multi-module project | Multiple `mod` declarations, qualified calls | 2 |
| 24 | `test-demo/` (subdir) | Test submodule | `import [super [*]]`, `import [testing [*]]` | 4 |

**\* Ring 0 core**: These files demonstrate Ring 0 concepts (Int arithmetic, Bool logic, recursion) but their prototype implementations use `print`/`show`/`do`/`platform`, which require Ring 4 IO. The Ring 0 reimplementation examples will use REPL evaluation instead of `print`.

### Observations

1. **No pure Ring 0 examples exist** — every prototype example uses `(platform stdio)` and `print` for output, making them all Ring 4 programs. Ring 0 examples must be REPL-first: each example is an expression or definition entered at the REPL, with the `:Type value` display confirming the result.
2. **Feature-oriented, not sequential** — each file demonstrates one feature area but assumes familiarity with others. The learning sequence must enforce "one new concept per example."
3. **13 of 24 examples require Ring 2+** — traits, modules, macros, and IO dominate the prototype's example set. The learning sequence needs more depth at Rings 0 and 1.
4. **Multi-file examples exist only at Ring 2** — module imports require the module system.

## 2. Learning Sequence Design

### Design Principles

1. **One new concept per example.** Each example introduces exactly one language feature.
2. **Simplest possible demonstration.** Minimal code that makes the concept clear.
3. **Cumulative.** Each example may use features from all prior examples — nothing else.
4. **REPL-first for Rings 0-1.** Ring 0 and Ring 1 examples are REPL sessions showing input and `:Type value` output. Batch programs (with `main`) begin at Ring 4 when IO arrives.
5. **Comments explain the concept**, not the syntax. The REPL output teaches the syntax.

### Numbering Convention

Examples are numbered `01` through `30` (approximately). Each maps to one ring and one concept.

### Complete Learning Sequence

**Numbering note**: The delivered file numbering is contiguous (01-18 so far). Ring 0 was delivered as examples 01-08. Ring 1 continues as 09-14. Ring 2 is 15-17 (traits, modules, display). Ring 3 begins at 18 (macros). Constrained polymorphism is covered within 15-traits.cl. Multi-signature and auto-currying are deferred (batch mode issues). Future examples continue from 19.

| # | File | Ring | Concept | Status |
|---|------|------|---------|--------|
| 01 | `01-integers.cl` | 0 | Integer literals and arithmetic | delivered |
| 02 | `02-booleans.cl` | 0 | Boolean literals and comparisons | delivered |
| 03 | `03-let-bindings.cl` | 0 | Local names with let | delivered |
| 04 | `04-functions.cl` | 0 | Named functions (defn) | delivered |
| 05 | `05-recursion.cl` | 0 | Self-recursive functions and TCO | delivered |
| 06 | `06-enums.cl` | 0 | Enum types and pattern matching | delivered |
| 07 | `07-polymorphism.cl` | 0 | Let-polymorphism and type variables | delivered |
| 08 | `08-floats.cl` | 0 | Float literals and arithmetic | delivered |
| 09 | `09-strings.cl` | 1 | String type and operations | delivered |
| 10 | `10-adts.cl` | 1 | Product and sum types with fields | delivered |
| 11 | `11-destructuring.cl` | 1 | Pattern matching on data constructors | delivered |
| 12 | `12-closures.cl` | 1 | Anonymous functions and capture | delivered |
| 13 | `13-higher-order.cl` | 1 | Functions as arguments and return values | delivered |
| 14 | `14-vecs.cl` | 1 | Vec literals and operations | delivered |
| 15 | `15-traits.cl` | 2 | Trait-based operator dispatch + constrained poly | delivered |
| 16 | `16-modules/` | 2 | Multi-file programs with modules | delivered |
| 17 | `17-display.cl` | 2 | User-defined traits and Display | delivered |
| 18 | `18-macros.cl` | 3 | Macros: defmacro, quasiquote, multi-clause | delivered |
| 19 | Multi-Signature | 2 | Function overloading by type | planned (batch mode blocked) |
| 20 | Auto-Currying | 2 | Partial application | planned (batch mode blocked) |
| 21 | Threading Macros | 3 | Data pipeline composition | planned |
| 22 | Derive | 3 | Auto-generated trait impls | planned |
| 23 | Hello World | 4 | IO model and print | planned |
| 24 | IO Sequencing | 4 | do and bind! | planned |
| 25 | Interactive IO | 4 | User input | planned |
| 26 | Testing | 4 | Inline test modules | planned |

### Feature Coverage Verification

All language features from the spec are covered:

| Spec Section | Feature | Example # |
|---|---|---|
| §4.1 | Literals (Int, Float, Bool) | 01, 02, 03 |
| §4.3 | Let bindings | 05 |
| §4.4 | If expressions | 04 |
| §4.5 | Lambda expressions | 14 |
| §4.6 | Function application | 06 |
| §5.1.1 | Single-signature defn | 06 |
| §5.1.2 | Multi-signature defn | 20 |
| §5.1.3 | Auto-currying | 21 |
| §5.2 | Type definitions | 08, 12 |
| §5.3 | Trait declarations | 18 |
| §5.4 | Trait implementations | 18 |
| §5.5 | Macros | 24 |
| §6 | Pattern matching | 09, 13 |
| §7 | Traits + constrained polymorphism | 18, 19 |
| §8 | Modules and imports | 22 |
| §9 | Macro system + derive | 24, 25, 26 |
| §10 | IO model | 27, 28, 29 |
| §12.5 | Tail call optimization | 07 |
| Appendix A | Builtin operators | 01, 02, 03 |

## 3. Ring 0 Examples (Concrete)

Ring 0 provides: `Int`, `Bool`, `Float`, arithmetic/comparison operators (`+`, `-`, `*`, `/`, `=`, `<`, `>`, `<=`, `>=`, `not`), `if`, `let`, `defn`, `deftype` (nullary/enum), `match`, and let-polymorphism. No strings, no heap allocation, no IO, no closures.

Ring 0 examples are REPL sessions. Each example is a file containing a comment header explaining the concept, followed by REPL input/output pairs formatted as comments. The actual runnable content is the expressions themselves.

### Example 01: Integers

```clojure
;; 01-integers.cl — Integer literals and arithmetic
;;
;; Cranelisp integers are signed 64-bit values.
;; Arithmetic operators: + - * /

;; Integer literal
;; > 42
;; :primitives/Int 42

;; Addition
;; > (+ 1 2)
;; :primitives/Int 3

;; Subtraction
;; > (- 10 3)
;; :primitives/Int 7

;; Multiplication
;; > (* 6 7)
;; :primitives/Int 42

;; Division (integer, truncating)
;; > (/ 17 5)
;; :primitives/Int 3

;; Nested arithmetic
;; > (+ (* 3 4) (- 10 5))
;; :primitives/Int 17

;; Negative literals
;; > -7
;; :primitives/Int -7

;; Zero
;; > 0
;; :primitives/Int 0
```

### Example 02: Booleans

```clojure
;; 02-booleans.cl — Boolean literals and comparison operators
;;
;; Booleans are true or false. Comparison operators return Bool.

;; Boolean literals
;; > true
;; :primitives/Bool true

;; > false
;; :primitives/Bool false

;; Equality
;; > (= 1 1)
;; :primitives/Bool true

;; > (= 1 2)
;; :primitives/Bool false

;; Less than
;; > (< 2 3)
;; :primitives/Bool true

;; Greater than
;; > (> 5 3)
;; :primitives/Bool true

;; Less than or equal
;; > (<= 3 3)
;; :primitives/Bool true

;; Greater than or equal
;; > (>= 4 5)
;; :primitives/Bool false

;; Negation
;; > (not true)
;; :primitives/Bool false

;; > (not (= 1 2))
;; :primitives/Bool true
```

### Example 03: Floats

```clojure
;; 03-floats.cl — Float literals and arithmetic
;;
;; Floats are IEEE 754 double-precision values.
;; The same arithmetic operators work on floats.

;; Float literal
;; > 3.14
;; :primitives/Float 3.14

;; Float arithmetic
;; > (+ 1.5 2.5)
;; :primitives/Float 4.0

;; > (* 3.14 2.0)
;; :primitives/Float 6.28

;; > (/ 10.0 3.0)
;; :primitives/Float 3.3333333333333335

;; > (- 1.0 0.5)
;; :primitives/Float 0.5

;; Float comparison
;; > (< 1.0 2.0)
;; :primitives/Bool true

;; > (= 3.14 3.14)
;; :primitives/Bool true
```

### Example 04: Conditionals

```clojure
;; 04-conditionals.cl — If expressions
;;
;; (if condition then-expr else-expr)
;; Both branches must have the same type. The condition must be Bool.

;; Simple if
;; > (if true 1 2)
;; :primitives/Int 1

;; > (if false 1 2)
;; :primitives/Int 2

;; Comparison in condition
;; > (if (> 5 3) 10 20)
;; :primitives/Int 10

;; Nested if
;; > (if (= 1 1) (if (< 2 3) 100 200) 300)
;; :primitives/Int 100

;; If with arithmetic
;; > (if (> 10 5) (+ 1 2) (* 3 4))
;; :primitives/Int 3

;; Both branches must agree in type
;; > (if true 42 0)
;; :primitives/Int 42
```

### Example 05: Let Bindings

```clojure
;; 05-let-bindings.cl — Local names with let
;;
;; (let [name1 value1 name2 value2 ...] body)
;; Bindings are sequential: later bindings can use earlier ones.

;; Single binding
;; > (let [x 5] (+ x 1))
;; :primitives/Int 6

;; Multiple bindings
;; > (let [x 3 y 4] (+ x y))
;; :primitives/Int 7

;; Sequential bindings (y uses x)
;; > (let [x 10 y (* x 2)] (+ x y))
;; :primitives/Int 30

;; Nested let
;; > (let [x 5] (let [y (+ x 1)] (* x y)))
;; :primitives/Int 30

;; Shadowing
;; > (let [x 1] (let [x 2] x))
;; :primitives/Int 2

;; Let with if
;; > (let [temp 100] (if (> temp 50) temp 0))
;; :primitives/Int 100
```

### Example 06: Functions

```clojure
;; 06-functions.cl — Named functions with defn
;;
;; (defn name [param1 param2 ...] body)
;; The REPL displays the inferred type scheme and qualified name.

;; A function that doubles its argument
;; > (defn double [x] (* x 2))
;; :(Fn [primitives/Int] primitives/Int) user/double

;; > (double 21)
;; :primitives/Int 42

;; A function with two parameters
;; > (defn add [x y] (+ x y))
;; :(Fn [primitives/Int primitives/Int] primitives/Int) user/add

;; > (add 10 32)
;; :primitives/Int 42

;; A function using if
;; > (defn abs [x] (if (< x 0) (- 0 x) x))
;; :(Fn [primitives/Int] primitives/Int) user/abs

;; > (abs -7)
;; :primitives/Int 7

;; > (abs 5)
;; :primitives/Int 5

;; A function using let
;; > (defn sum-of-squares [a b] (let [a2 (* a a) b2 (* b b)] (+ a2 b2)))
;; :(Fn [primitives/Int primitives/Int] primitives/Int) user/sum-of-squares

;; > (sum-of-squares 3 4)
;; :primitives/Int 25
```

### Example 07: Recursion

```clojure
;; 07-recursion.cl — Self-recursive functions
;;
;; Functions can call themselves. Cranelisp supports tail call optimization
;; for self-recursive calls in tail position.

;; Factorial (not tail-recursive: * wraps the recursive call)
;; > (defn fact [n] (if (= n 0) 1 (* n (fact (- n 1)))))
;; :(Fn [primitives/Int] primitives/Int) user/fact

;; > (fact 0)
;; :primitives/Int 1

;; > (fact 5)
;; :primitives/Int 120

;; > (fact 10)
;; :primitives/Int 3628800

;; Factorial with accumulator (tail-recursive)
;; > (defn fact-acc [n acc] (if (= n 0) acc (fact-acc (- n 1) (* n acc))))
;; :(Fn [primitives/Int primitives/Int] primitives/Int) user/fact-acc

;; > (fact-acc 10 1)
;; :primitives/Int 3628800

;; > (fact-acc 20 1)
;; :primitives/Int 2432902008176640000

;; Fibonacci
;; > (defn fib [n] (if (<= n 1) n (+ (fib (- n 1)) (fib (- n 2)))))
;; :(Fn [primitives/Int] primitives/Int) user/fib

;; > (fib 10)
;; :primitives/Int 55

;; GCD (Euclidean algorithm, tail-recursive)
;; > (defn gcd [a b] (if (= b 0) a (gcd b (- a (* (/ a b) b)))))
;; :(Fn [primitives/Int primitives/Int] primitives/Int) user/gcd

;; > (gcd 48 18)
;; :primitives/Int 6
```

### Example 08: Enums

```clojure
;; 08-enums.cl — Enum types (nullary ADTs)
;;
;; (deftype Name Variant1 Variant2 ...)
;; All variants have no fields. Constructors accessed as Type.Variant.

;; Define an enum
;; > (deftype Color Red Green Blue)
;; :user/Color

;; Constructors are values
;; > Color.Red
;; :user/Color Color.Red

;; > Color.Green
;; :user/Color Color.Green

;; > Color.Blue
;; :user/Color Color.Blue

;; A function returning an enum
;; > (defn favorite [] Color.Blue)
;; :(Fn [] user/Color) user/favorite

;; > (favorite)
;; :user/Color Color.Blue

;; A second enum
;; > (deftype Direction North South East West)
;; :user/Direction

;; > Direction.North
;; :user/Direction Direction.North
```

### Example 09: Match

```clojure
;; 09-match.cl — Pattern matching on enums
;;
;; (match scrutinee [Pattern1 body1 Pattern2 body2 ...])
;; Patterns are tested top-to-bottom. Must be exhaustive.

;; Match on Color (from example 08)
;; > (deftype Color Red Green Blue)
;; :user/Color

;; > (defn color-to-int [c] (match c [Color.Red 1 Color.Green 2 Color.Blue 3]))
;; :(Fn [user/Color] primitives/Int) user/color-to-int

;; > (color-to-int Color.Red)
;; :primitives/Int 1

;; > (color-to-int Color.Green)
;; :primitives/Int 2

;; > (color-to-int Color.Blue)
;; :primitives/Int 3

;; Wildcard pattern
;; > (defn is-red [c] (match c [Color.Red true _ false]))
;; :(Fn [user/Color] primitives/Bool) user/is-red

;; > (is-red Color.Red)
;; :primitives/Bool true

;; > (is-red Color.Blue)
;; :primitives/Bool false

;; Match with computation in body
;; > (defn color-score [c] (match c [Color.Red (* 10 1) Color.Green (* 10 2) Color.Blue (* 10 3)]))
;; :(Fn [user/Color] primitives/Int) user/color-score

;; > (color-score Color.Blue)
;; :primitives/Int 30

;; Boolean "enum" with if vs match
;; > (deftype Answer Yes No)
;; :user/Answer

;; > (defn answer-to-int [a] (match a [Answer.Yes 1 Answer.No 0]))
;; :(Fn [user/Answer] primitives/Int) user/answer-to-int

;; > (answer-to-int Answer.Yes)
;; :primitives/Int 1
```

### Example 10: Polymorphism

```clojure
;; 10-polymorphism.cl — Let-polymorphism and type variables
;;
;; Functions inferred with type variables work on any type.
;; The REPL shows type variables as lowercase letters: a, b, c...

;; The identity function
;; > (defn id [x] x)
;; :(Fn [a] a) user/id

;; Works on Int
;; > (id 42)
;; :primitives/Int 42

;; Works on Bool
;; > (id true)
;; :primitives/Bool true

;; Works on Float
;; > (id 3.14)
;; :primitives/Float 3.14

;; A polymorphic function with two parameters
;; > (defn first-of [a b] a)
;; :(Fn [a b] a) user/first-of

;; > (first-of 1 2)
;; :primitives/Int 1

;; > (first-of true 42)
;; :primitives/Bool true

;; A polymorphic function using if
;; > (defn choose [flag x y] (if flag x y))
;; :(Fn [primitives/Bool a a] a) user/choose

;; > (choose true 10 20)
;; :primitives/Int 10

;; > (choose false 10 20)
;; :primitives/Int 20

;; Works on enum too (given deftype Color from earlier)
;; > (deftype Color Red Green Blue)
;; :user/Color

;; > (choose true Color.Red Color.Blue)
;; :user/Color Color.Red
```

### Ring 0 Acceptance Criteria Coverage

| Acceptance Criterion | Example(s) |
|---|---|
| `(+ 1 2)` -> `:primitives/Int 3` | 01 |
| `(defn id [x] x)` -> `:(Fn [a] a) user/id` | 10 |
| `(if true 1 2)` -> `:primitives/Int 1` | 04 |
| `(let [x 5] (+ x 1))` -> `:primitives/Int 6` | 05 |
| `(deftype Color Red Green Blue)` + match | 08, 09 |
| `(defn fact [...])` runs correctly | 07 |
| Batch/REPL identical results | All (REPL session format) |
| REPL experience tests pass | All (`:Type value` format demonstrated) |

## 4. Ring 1 Examples (Concrete)

Ring 1 adds: `String` type, heap allocation (ADTs with fields, closures), reference counting. Vec and List deferred to Sprint 3.

**Note on numbering**: Ring 0 examples were delivered as 01-08. Ring 1 examples continue as 09-13 (renumbered from the original plan's 11-15 to maintain a contiguous sequence). Vec (16) and List (17) are deferred.

### Example 09: Strings

```clojure
;; String literals, concatenation, equality, conversion.
;; Since batch programs return Int from main, we use str-len
;; and str-eq to convert string results to integers.

;; String literal length
(defn test-literal-len [] (str-len "hello"))     ;; -> 5

;; Concatenation produces a new string
(defn test-concat []
  (str-len (str-concat "hello" " world")))       ;; -> 11

;; String equality
(defn test-eq []
  (if (str-eq "abc" "abc") 1 0))                 ;; -> 1

;; Convert an integer to a string
(defn test-int-to-string []
  (str-len (int-to-string 42)))                  ;; -> 2

;; Strings in let bindings
(defn test-let-string []
  (let [greeting "hello"
        name     "world"
        msg      (str-concat (str-concat greeting ", ") name)]
    (str-len msg)))                               ;; -> 12

;; Strings passed to and returned from functions
(defn make-greeting [who]
  (str-concat "hello, " who))

(defn test-fn-string []
  (str-len (make-greeting "cranelisp")))          ;; -> 16
```

**Covers**: string literals, `str-concat`, `str-eq`, `str-len`, `int-to-string`, `float-to-string`, `bool-to-string`, strings in let bindings, strings as function args/returns.
**Expected main return**: 55

### Example 10: ADTs with Fields

```clojure
;; Product types, sum types, polymorphic ADTs, shortcut syntax.

;; Product type: a 2D point
(deftype Point [:Int x :Int y])
(defn get-x [p] (match p [(Point px py) px]))

;; Sum type: polymorphic Option
(deftype (Option a) None (Some [:a val]))
(defn unwrap-or [opt default]
  (match opt [(Some x) x  None default]))

;; Two-constructor sum type
(deftype (Either a b) (Left [:a val]) (Right [:b val]))

;; Shortcut syntax: bare field names, types inferred
(deftype Pair [first second])
```

**Covers**: product types with typed fields, polymorphic sum types, Either (two data constructors), shortcut syntax, constructors as function calls, ADTs returned from functions.
**Expected main return**: 265

### Example 11: Destructuring Match

```clojure
;; Pattern matching on data constructors to extract fields.

;; Constructor pattern binds fields
(match (Point 3 4) [(Point x y) (add-i64 x y)])  ;; -> 7

;; Sum type discrimination
(match (Some 42) [(Some x) x  None 0])            ;; -> 42

;; Wildcard ignores the value
(match (Some 42) [(Some _) 1  _ 0])                ;; -> 1

;; Nested match for chained operations
(defn add-opts [a b]
  (match a
    [None 0
     (Some x) (match b [None x  (Some y) (add-i64 x y)])]))

;; Safe division returning Option + chained match
(defn safe-div [a b]
  (if (eq-i64 b 0) None (Some (div-i64 a b))))
```

**Covers**: product destructuring, sum type discrimination, wildcard `_`, variable binding patterns, nested match, practical use (safe division with Option chaining).
**Expected main return**: 69

### Example 12: Closures

```clojure
;; Anonymous functions (fn) and variable capture.

;; Immediate call
((fn [x] (add-i64 x 1)) 5)                        ;; -> 6

;; Lambda in let binding
(let [double (fn [x] (mul-i64 x 2))] (double 21)) ;; -> 42

;; Closure captures a variable
(let [n 10] ((fn [x] (add-i64 n x)) 32))          ;; -> 42

;; Function returning a closure (factory pattern)
(defn make-adder [n] (fn [x] (add-i64 n x)))
((make-adder 10) 32)                               ;; -> 42

;; Nested closures
(let [a 1]
  (let [f (fn [x] (add-i64 a x))]
    (let [g (fn [y] (f y))] (g 9))))               ;; -> 10
```

**Covers**: anonymous functions, zero/multi-parameter lambdas, single and multiple variable capture, boolean capture, closures as return values, factory pattern, nested closures, closure in if branches.
**Expected main return**: 263

### Example 13: Higher-Order Functions

```clojure
;; Functions as arguments and return values.

;; Apply a function to a value
(defn apply-fn [f x] (f x))

;; Apply a function twice
(defn apply-twice [f x] (f (f x)))

;; Apply n times (recursion + higher-order)
(defn repeat-fn [f n x]
  (if (eq-i64 n 0) x (repeat-fn f (sub-i64 n 1) (f x))))

;; Named functions as values
(defn inc [x] (add-i64 x 1))
(apply-fn inc 41)                                   ;; -> 42

;; Function composition
(defn compose [f g] (fn [x] (f (g x))))
((compose inc double) 10)                           ;; -> 21

;; Pipeline: chain three transformations
(defn pipeline3 [f g h x] (h (g (f x))))
```

**Covers**: functions as arguments, apply-twice, recursive apply-n-times, named functions passed as values, function factories, function composition via compose, transform-and-check pattern, three-stage pipeline.
**Expected main return**: 203

### Ring 1 Acceptance Criteria Coverage

| Acceptance Criterion | Example(s) |
|---|---|
| String literals | 09 |
| `str-concat`, `str-eq`, `str-len` | 09 |
| `int-to-string`, `bool-to-string` | 09 |
| Product types with typed fields | 10, 11 |
| Polymorphic sum types (Option) | 10, 11 |
| Data-constructor match with field binding | 11 |
| Wildcard `_` in data match | 11 |
| Nested match | 11 |
| Lambda expressions (fn) | 12 |
| Variable capture (closures) | 12 |
| Closures as return values | 12, 13 |
| Higher-order function application | 13 |
| Function composition | 13 |
| Named functions as values | 13 |

### Deferred to Sprint 3

Examples 16 (Vectors) and 17 (Lists) are deferred alongside Vec (Chunk D).

## 5. Ring 2 Examples (Outline)

Ring 2 adds: traits, trait implementations, constrained polymorphism, monomorphisation, multi-signature dispatch, modules, imports/exports.

### Example 15: Traits (delivered)

Demonstrates Num/Eq/Ord trait-based operator dispatch:
- `(+ 3 4)`, `(- 10 3)`, `(* 6 7)`, `(/ 20 4)` on Int
- `(+ 1.5 2.5)`, `(* 3.0 4.0)` on Float
- `(= 42 42)` on Int, Float, Bool, String
- `(< 3 5)` on Int and Float
- Trait operators in recursive functions (factorial, sum-to)
- Trait operators inside closures and match bodies
- Named primitives remain available alongside trait dispatch

**Not yet demonstrated** (pending compiler fixes):
- User-defined traits with `deftrait`/`impl` (GOT slot issue in batch)
- Default methods (`!=`, `>`, `<=`, `>=`) (GOT slot issue in batch)
- Constrained polymorphism (codegen issue for separate constrained+caller defns)

### Example 16: Constrained Polymorphism

- `(defn add [x y] (+ x y))` inferred as `:(Fn [:Num a :a] a)`
- `(add 1 2)` -> Int, `(add 1.5 2.5)` -> Float
- Monomorphisation at call sites

### Example 17: Multi-Signature Dispatch

- `(defn size ([:Vec v] (vec-len v)) ([:List l] (list-len l)))`
- Static dispatch based on argument type

### Example 18: Auto-Currying

- `(+ 1)` returns a closure
- `(map (+ 1) [1 2 3])` -> `[2 3 4]`

### Example 19: Modules (Multi-File)

**Structure**: A directory `19-modules/` with two files demonstrating cross-file module organization.

**`19-modules/main.cl`** (entry point):
- Declares an inline module: `(mod util)` — signals that `util.cl` exists alongside `main.cl`
- Imports a specific helper: `(import [util [double]])`
- Uses the imported name bare: `(double 21)` -> 42
- Also demonstrates qualified access: `(util/double 10)` -> 20
- Shows that unimported names require qualification: `util/triple` works, bare `triple` does not

**`19-modules/util.cl`** (helper module):
- Exports public functions: `(export [double triple])`
- `(defn double [x] (* x 2))` — public, importable
- `(defn triple [x] (* x 3))` — public, accessible as `util/triple`
- `(defn- helper [x] (+ x 1))` — private, not visible from `main.cl`

**Concepts demonstrated**:
1. `(mod name)` declares a companion file
2. File resolution: `util.cl` found next to `main.cl`
3. `(import [util [double]])` selective import — bare name access
4. `util/triple` qualified name access without import
5. `(export [...])` controls what is visible
6. `defn-` makes definitions private to their module

**Depends on**: All Ring 0-1 examples (01-14) plus Ring 2 module system.
**Cannot be delivered until**: Cross-module imports are fully wired in the compiler.

### Example 20: Lazy Sequences

- `(range-from 0)` infinite sequence
- `(take 5 (range-from 0))` finite slice
- `(iterate (fn [x] (* x 2)) 1)` from seed
- `(filter (fn [x] (> x 2)) [1 2 3 4 5])`

## 6. Ring 3 Examples (Outline)

Ring 3 adds: macros (`defmacro`), quasiquote, multi-clause macros, derive, prelude macros (`->`, `->>`, `cond`, `case`, `vec`, `list`).

### Example 21: Macros

- `(defmacro my-inc [x] \`(+ ~x 1))`
- Quasiquote with unquote
- `(my-inc 41)` -> `:primitives/Int 42`

### Example 22: Threading Macros

- `(-> 5 (+ 1) (* 2))` thread-first
- `(->> [1 2 3] (map inc) (filter (fn [x] (> x 2))))` thread-last
- Data pipeline style

### Example 23: Derive

- `(derive [Eq Ord Display] (deftype Color Red Green Blue))`
- `(= Color.Red Color.Red)` -> `true`
- `(show Color.Green)` -> `"Green"`

## 7. Ring 4 Examples (Outline)

Ring 4 adds: IO model (platform, `print`, `read-line`), `do`/`bind!`/`pure` macros, `main` entry point, parallel evaluation, testing infrastructure.

### Example 24: Hello World

- `(platform stdio)`, `(import [platform.stdio [*]])`
- `(defn main [] (print "hello, world!"))`
- First batch-mode program

### Example 25: IO Sequencing

- `do` for sequencing IO actions
- `bind!` for capturing IO results
- `pure` for wrapping values in IO

### Example 26: Interactive IO

- `read-line`, `parse-int`
- IO loop with recursion
- Error handling with `Option` in IO context

### Example 27: Testing

- `(mod test)` inline test submodule
- `(import [testing [*]])`, `assert-eq`, `check`
- `/run-tests` to discover and execute tests

## 8. Appendix B Cross-Reference

The spec's Appendix B contains 13 extended examples. Each maps to one or more learning-sequence examples (using delivered numbering):

| Appendix B | Learning Sequence | Notes |
|---|---|---|
| B.1 Hello World | 25 | Deferred to Ring 4 (IO) |
| B.2 Factorial | 05 | Ring 0 (recursion) |
| B.3 Algebraic Data Types | 06, 10, 11 | Ring 0 (enums) and Ring 1 (fields, destructuring) |
| B.4 IO with bind! | 27 | Ring 4 |
| B.5 Lazy Sequences | 21 | Ring 2 |
| B.6 Macros | 22 | Ring 3 |
| B.7 Higher-Order Functions | 12, 13 | Ring 1 |
| B.8 Threading Macros | 23 | Ring 3 |
| B.9 Multi-Signature Dispatch | 18 | Ring 2 |
| B.10 Constrained Polymorphism | 17 | Ring 2 |
| B.11 IO Sequencing with do | 26 | Ring 4 |
| B.12 Conditional IO with pure | 26 | Ring 4 (combined into IO Sequencing) |
| B.13 Combining do and bind! | 27 | Ring 4 (combined into Interactive IO) |

## 9. File Structure

```
examples/
  plan-examples.md      — this file
  01-integers.cl        — delivered (Ring 0)
  02-booleans.cl        — delivered (Ring 0)
  03-let-bindings.cl    — delivered (Ring 0)
  04-functions.cl       — delivered (Ring 0)
  05-recursion.cl       — delivered (Ring 0)
  06-enums.cl           — delivered (Ring 0)
  07-polymorphism.cl    — delivered (Ring 0)
  08-floats.cl          — delivered (Ring 0)
  09-strings.cl         — delivered (Ring 1)
  10-adts.cl            — delivered (Ring 1)
  11-destructuring.cl   — delivered (Ring 1)
  12-closures.cl        — delivered (Ring 1)
  13-higher-order.cl    — delivered (Ring 1)
  14-vecs.cl            — delivered (Ring 1, Sprint 3)
  15-traits.cl          — delivered (Ring 2A, Sprint 4)
  16-modules/           — delivered (Ring 2, Sprint 12, multi-file)
  17-display.cl         — delivered (Ring 2, Sprint 12)
  18-macros.cl          — delivered (Ring 3, Sprint 12)
  19-multi-sig.cl       — planned (Ring 2, blocked: batch mode)
  20-auto-curry.cl      — planned (Ring 2, blocked: batch mode)
  21-threading.cl       — planned (Ring 3)
  22-derive.cl          — planned (Ring 3)
  23-hello-world.cl     — planned (Ring 4)
  24-io-sequencing.cl   — planned (Ring 4)
  25-interactive-io.cl  — planned (Ring 4)
  26-testing/           — planned (Ring 4, multi-file)
```

## 10. Ring 3 Readiness Assessment (Sprint 9)

Survey of sketch examples classified by Ring 3 readiness. Each sketch example is assessed for macro forms used and IO dependency.

### Sketch Example Classification

| # | File | Macro forms used | IO required? | Ring readiness |
|---|------|-----------------|--------------|----------------|
| 1 | `hello.cl` | none | yes (`platform`, `print`) | Ring 4 |
| 2 | `factorial.cl` | none | yes (`platform`, `print`) | Ring 4 (but core logic is Ring 0; already ported as example 07) |
| 3 | `strings.cl` | `do` | yes (`platform`, `print`) | Ring 4 |
| 4 | `float.cl` | `do` | yes (`platform`, `print`, `pure`) | Ring 4 |
| 5 | `closure.cl` | `do` | yes (`platform`, `print`) | Ring 4 |
| 6 | `list.cl` | `do`, `list` | yes (`platform`, `print`) | Ring 4 |
| 7 | `vec.cl` | `do` | yes (`platform`, `print`, `pure`) | Ring 4 |
| 8 | `seq.cl` | `do` | yes (`platform`, `print`) | Ring 4 |
| 9 | `curry.cl` | `do` | yes (`platform`, `print`, `pure`) | Ring 4 |
| 10 | `adt.cl` | `do` | yes (`platform`, `print`) | Ring 4 |
| 11 | `functor.cl` | `do`, `list` | yes (`platform`, `print`) | Ring 4 |
| 12 | `mapfold.cl` | `do`, `list` | yes (`platform`, `print`) | Ring 4 |
| 13 | `threading.cl` | `do`, `->`, `->>`, `cond`, `case`, `vec` | yes (`platform`, `print`) | Ring 4 |
| 14 | `dot_notation.cl` | `do` | yes (`platform`, `print`) | Ring 4 |
| 15 | `sum-input.cl` | `do`, `bind!` | yes (`platform`, `print`, `read-line`, `pure`) | Ring 4 |
| 16 | `reader.cl` | `do`, quasiquote (`` ` ``), `defmacro` | yes (`platform`, `print`) | Ring 4 |
| 17 | `derived.cl` | `do`, `derive` | yes (`platform`, `print`, `pure`) | Ring 4 |
| 18 | `macro.cl` | `do`, `defmacro`, `slist`, `SexpList`, `SexpSym`, `SexpInt` | yes (`platform`, `print`, `pure`) | Ring 4 |
| 19 | `test-demo.cl` | `mod` | yes (`run-tests` + testing infra) | Ring 4 |
| 20 | `parallel.cl` | `bind!`, `par-let` | yes (`platform`, `print`, `pure`) | Ring 4 |
| 21 | `traits.cl` | none | yes (`platform`, `print`) | Ring 4 |

### Analysis

**All 21 sketch examples require IO** (all use `(platform stdio)` and `print`). There are no pure-computation sketch examples. This is expected — the sketch was designed for batch execution, not REPL evaluation.

**Macro forms appearing in sketch examples**:

| Macro | Count of examples using it |
|-------|--------------------------|
| `do` | 16 |
| `list` | 3 (`list.cl`, `functor.cl`, `mapfold.cl`) |
| `bind!` | 2 (`sum-input.cl`, `parallel.cl`) |
| `->` | 1 (`threading.cl`) |
| `->>` | 1 (`threading.cl`) |
| `cond` | 1 (`threading.cl`) |
| `case` | 1 (`threading.cl`) |
| `vec` | 1 (`threading.cl`) |
| `derive` | 1 (`derived.cl`) |
| `defmacro` | 2 (`reader.cl`, `macro.cl`) |

### Impact on Learning Sequence Examples 21-23

The planned Ring 3 learning examples (21-Macros, 22-Threading, 23-Derive) are **REPL-first** and do not require IO. They can be implemented as soon as the macro pipeline is functional:

| Example | Macro features needed | IO needed? | Implementable at |
|---------|----------------------|------------|-------------------|
| 21 — Macros | `defmacro`, quasiquote, `SexpList`/`SexpSym`/`SexpInt` constructors | no (REPL) | Ring 3, after macro pipeline |
| 22 — Threading | `->`, `->>`, `cond`, `case`, `vec` | no (REPL) | Ring 3, after prelude macros |
| 23 — Derive | `derive` macro | no (REPL) | Ring 3, after derive infrastructure |

**Ring 3 porting opportunity**: Several sketch examples have pure-computation cores that can be extracted as REPL examples once macros are available. For instance, `threading.cl`'s `->`, `->>`, `cond`, `case` demonstrations can be ported directly as REPL input/output pairs (stripping the `do`/`print` IO wrapper). Similarly, `derived.cl`'s derive demonstrations and `macro.cl`'s defmacro demonstrations are pure-computation at their core.

### Conclusion

Ring 3 examples (21-23) are self-contained and do not depend on IO. They can proceed as soon as the macro pipeline lands. Ring 4 examples (24-27) depend on the IO model and platform system. No sketch example can be ported verbatim before Ring 4 due to universal `(platform stdio)` dependency, but the learning-sequence examples are designed as REPL sessions and avoid this constraint.

## 11. Ring 3 Learning Examples (Sprint 11 Plan)

Sprint 11 wires macros into the batch/REPL pipelines and delivers prelude macros. Once that lands, four new REPL-first examples can be built. All are pure computation -- no IO required.

### Example 21: `macro-basics.cl`

**Demonstrates**: `defmacro`, quasiquote (`` ` ``), unquote (`~`), `/expand` REPL command.

Defines simple single-clause macros (`when`, `unless`, `my-and`) using quasiquote templates. Shows how macro expansion works by inspecting output with `/expand`. Illustrates the `Sexp` return-type constraint and the distinction between compile-time transformation and runtime evaluation.

- **Macro features**: `defmacro`, quasiquote, unquote, single-clause
- **Prelude macros used**: none (all user-defined)
- **REPL-only**: yes -- no IO needed; expressions evaluate and display results

### Example 22: `multi-clause-macro.cl`

**Demonstrates**: Multi-clause `defmacro` with arity dispatch, rest params (`&`), recursive macro expansion.

Builds a `log` macro with 1-arg and 2-arg forms (arity dispatch), then a recursive `my-list` macro that uses a base clause `([] ...)` and a step clause `([x & rest] ...)` to construct a List from arguments. Shows clause ordering and how the first matching clause wins.

- **Macro features**: multi-clause `defmacro`, `& rest` params, recursive expansion, clause dispatch
- **Prelude macros used**: none (all user-defined; uses `Cons`/`Nil` constructors for list building)
- **REPL-only**: yes -- all results observable via REPL display

### Example 23: `prelude-macros.cl`

**Demonstrates**: Using prelude-provided macros: `list`, `cond`, `case`, `->`, `->>`, `vec`.

No user-defined macros -- this example exercises the macros that ship with the prelude. Shows data construction (`list`, `vec`), multi-way conditionals (`cond`, `case`), and data-pipeline composition (`->`, `->>`). Uses `/expand` to reveal the generated code behind each macro call.

- **Macro features**: prelude macro usage (not definition)
- **Prelude macros used**: `list`, `cond`, `case`, `->`, `->>`, `vec`
- **REPL-only**: yes -- all results observable via REPL display

### Example 24: `custom-control-flow.cl`

**Demonstrates**: Building a control-flow abstraction with macros -- a `for-each` macro that iterates a function over a list, and a `with-default` macro that unwraps an Option or substitutes a default.

Shows how macros enable user-defined syntax that looks like built-in control flow. Uses bracket destructuring (`[name expr]` parameter patterns) and splicing unquote (`~@`). Combines user macros with prelude macros (`list`, `cond`) to build higher-level abstractions.

- **Macro features**: bracket destructuring params, splicing unquote (`~@`), composing macros
- **Prelude macros used**: `list`, `cond`
- **REPL-only**: yes -- all results observable via REPL display

### Numbering Impact

These four examples shift the existing Ring 4 plan forward:

| Old # | New # | File |
|-------|-------|------|
| 24 | 25 | `hello-world.cl` |
| 25 | 26 | `io-sequencing.cl` |
| 26 | 27 | `interactive-io.cl` |
| 27 | 28 | `testing/` |

The `derive` example (previously outlined as example 23 in section 6) is absorbed into `prelude-macros.cl` or deferred to a dedicated example if `derive` infrastructure lands in Sprint 11.

---

## Next skills

- `/docs` -- Getting-started tutorial can reference examples 09-13 for Ring 1 content; update tutorial sections 14-18, 21
- `/qa` -- Ring 1 integration tests are passing; file FIXMEs on relevant docs for any Ring 1 example findings
- `/repl` -- REPL experience tests for Ring 1 heap type display (strings, ADTs, closures)
- `/review` -- Ring gate review can confirm examples 09-13 exercise all Ring 1 acceptance criteria
