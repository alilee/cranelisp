# Appendix B: Example Programs

**Non-normative reference-library examples.** These programs illustrate a supplied
library, not prerequisites for the language. Each imports the reference
`prelude` module explicitly, as well as `primitives` and the declared platform.
The macros (`do`, `bind!`, `list`, `cond`, `str`, `->`, `->>`, `vec`), traits,
operators, collection ADTs and helpers are library bindings. `pure`, `bind`,
`parse-int`, `str-concat` and the seeded ADTs are compiler-provided names.
Local `Maybe` and `Tuple` declarations in B.3 are illustrative ADTs, distinct
from the seeded `Option` and `Pair`.
B.6 also explicitly imports compiler-provided macro data and optional SList
library helpers. The examples' library-specific results do not constrain
another library or an empty-prelude program (§8.8.3).

## B.1 Hello World [Uncovered S124 — was S10]

A program using the reference library's `show` function.

```clojure
(platform stdio)
(import [primitives [*] prelude [*] platform.stdio [*]])

(defn main []
  (print (show 42)))
```

Output: `42`

## B.2 Factorial (Recursion) [Uncovered S124 — was S10]

Recursive function with conditional and arithmetic.

```clojure
(platform stdio)
(import [primitives [*] prelude [*] platform.stdio [*]])

(defn fact [n]
  (if (= n 0)
    1
    (* n (fact (- n 1)))))

(defn main []
  (print (show (fact 10))))
```

Output: `3628800`

## B.3 Algebraic Data Types [Uncovered S124 — was S10]

Product types, sum types, enums, pattern matching, and trait implementations for ADTs.

```clojure
(platform stdio)
(import [primitives [*] prelude [*] platform.stdio [*]])

;; Product type (struct-like)
(deftype Point [:Int x :Int y])

;; Sum type (tagged union)
(deftype (Maybe a) Nothing (Just [:a val]))

;; Enum (all-nullary sum type)
(deftype Color Red Green Blue)

;; Polymorphic product
(deftype (Tuple a b) [:a first :b second])

;; Constructor + match
(defn get-x [p]
  (match p
    [(Point px py) px]))

(defn color-value [c]
  (match c
    [Red 1
     Green 2
     Blue 3]))

(defn unwrap-or [opt default]
  (match opt
    [Nothing default
     (Just x) x]))

;; Trait impl for enum ADT
(impl Display Color
  (defn show [c]
    (match c
      [Red "Red"
       Green "Green"
       Blue "Blue"])))

;; Polymorphic trait impl
(impl Display (Maybe :Display a)
  (defn show [self]
    (match self
      [Nothing "Nothing"
       (Just x) (show x)])))

(defn main []
  (do
    (print (show (get-x (Point 3 4))))
    (print (show (color-value Green)))
    (print (show (unwrap-or (Just 42) 0)))
    (print (show (unwrap-or Nothing 99)))
    (print (show Red))
    (print (show (Just 42)))
    (print (show (Just 3.14)))))
```

Output:
```
3
2
42
99
Red
42
3.14
```

## B.4 IO with bind! [Uncovered S124 — was S10]

Reading input, parsing, and error handling with monadic IO.

```clojure
(platform stdio)
(import [primitives [*] prelude [*] platform.stdio [*]])

(defn read-int []
  (bind! [line (read-line)]
    (pure (parse-int line))))

(defn sum-loop [remaining acc]
  (if (= remaining 0)
    (pure acc)
    (bind! [result (read-int)]
      (match result
        [(Some n) (sum-loop (- remaining 1) (+ acc n))
         None (do
          (print "Invalid number, try again")
          (sum-loop remaining acc))]))))

(defn main []
  (bind! [total (sum-loop 6 0)]
    (print (show total))))
```

## B.5 Lazy Sequences [Uncovered S124 — was S17]

Infinite sequences, lazy operations, and the unified collection API.

```clojure
(platform stdio)
(import [primitives [*] prelude [*] platform.stdio [*]])

(defn main []
  (do
    ;; take 5 from an infinite range
    (print (show (head (to-list (take 5 (range-from 0))))))

    ;; lazy map + take from infinite sequence
    (print (show (head (to-list (take 3 (map inc (range-from 10)))))))

    ;; reduce over a finite lazy seq
    (print (show :Int (reduce + 0 (lazy-take 5 (range-from 1)))))

    ;; iterate: powers of 2
    (print (show (head (to-list (lazy-drop 5
      (lazy-take 10 (iterate (fn [x] (* x 2)) 1)))))))

    ;; filter: only values > 2
    (print (show (head (to-list (filter (fn [x] (> x 2)) [1 2 3 4 5])))))

    ;; repeat
    (print (show (head (to-list (lazy-take 3 (repeat 42))))))))
```

Output:
```
0
11
15
32
3
42
```

## B.6 Macros [Uncovered S124 — was S17]

Compile-time code transformation with `defmacro`.

```clojure
(platform stdio)
(import [primitives [*] macros [*] core.syntax [slist]
         prelude [*] platform.stdio [*]])

;; A simple macro: wraps expression in (+ expr 1)
(defmacro my-inc [x]
  (SexpList (slist (SexpSym "+") x (SexpInt 1))))

;; Using quasiquote for cleaner syntax
(defmacro when [cond body]
  `(if ~cond (Some ~body) None))

;; Variadic macro
(defmacro my-add [& args]
  `(+ ~@args))

(defn main []
  (do
    (print (show (my-inc 41)))       ; → 42
    (print (show (when true 99)))    ; → Some 99
    (print (show (my-add 10 20)))))  ; → 30
```

## B.7 Higher-Order Functions and Closures [Uncovered S124 — was S17]

First-class functions, closures, and auto-currying.

```clojure
(platform stdio)
(import [primitives [*] prelude [*] platform.stdio [*]])

;; Higher-order function
(defn apply-twice [f x]
  (f (f x)))

;; Closure: returns a function that captures n
(defn make-adder [n]
  (fn [x] (+ n x)))

;; Auto-currying: (+ 10) is a function that adds 10
(defn main []
  (let [add10 (make-adder 10)
        double (fn [x] (* x 2))
        add5 (+ 5)]
    (do
      (print (show (add10 32)))           ; → 42
      (print (show (apply-twice double 3))) ; → 12
      (print (show (add5 37))))))         ; → 42
```

## B.8 Threading Macros [Uncovered S124 — was S17]

Data transformation pipelines with `->` and `->>`.

```clojure
(platform stdio)
(import [primitives [*] prelude [*] platform.stdio [*]])

(defn main []
  (do
    ;; thread-first: result threaded as first argument
    (print (show (-> 10
                   (+ 5)
                   (* 2))))         ; (+ 10 5) → 15, (* 15 2) → 30

    ;; thread-last: result threaded as last argument
    (print (show (->> [1 2 3 4 5]
                   (map inc)
                   (filter (fn [x] (> x 3)))
                   (reduce + 0))))))  ; → 9 (4+5)
```

## B.9 Multi-Signature Dispatch [Uncovered S124 — was S17]

Functions with multiple implementations dispatched by argument type.

```clojure
(platform stdio)
(import [primitives [*] prelude [*] platform.stdio [*]])

;; map dispatches on container type
(defn main []
  (let [double (fn [x] (* x 2))]
    (do
      ;; Vec input → lazy Seq output
      (print (show (head (to-list (map double [1 2 3])))))

      ;; List input → lazy Seq output
      (print (show (head (to-list (map double (list 10 20 30))))))

      ;; Seq input → lazy Seq output
      (print (show (head (to-list
        (take 3 (map double (range-from 1))))))))))
```

Output:
```
2
20
2
```

## B.10 Constrained Polymorphism [Uncovered S124 — was S10]

Functions that work across types sharing a trait.

```clojure
(platform stdio)
(import [primitives [*] prelude [*] platform.stdio [*]])

;; add works for any Num type — monomorphised at call site
(defn add [x y] (+ x y))

;; double works for any Num type
(defn double [x] (+ x x))

(defn main []
  (do
    (print (show (add 1 2)))         ; Int version: add$Int+Int
    (print (show (add 1.5 2.5)))     ; Float version: add$Float+Float
    (print (show (double 21)))       ; Int version
    (print (show (double 3.14)))))   ; Float version
```

Output:
```
3
4.0
42
6.28
```

## B.11 IO Sequencing with `do` [Uncovered S124 — was S10]

Evaluating multiple IO actions, discarding intermediate results.

```clojure
(platform stdio)
(import [primitives [*] prelude [*] platform.stdio [*]])

(defn main []
  (do
    (print "hello, world!")
    (print (show 42))
    (print (show true))))
```

`do` sequences three `print` calls. The first two results are discarded; the return value is the result of the last `print`. Output:
```
hello, world!
42
true
```

## B.12 Conditional IO with `pure` [Uncovered S124 — was S10]

Using `pure` to satisfy branch type requirements.

```clojure
(platform stdio)
(import [primitives [*] prelude [*] platform.stdio [*]])

(defn maybe-print [x]
  (if (> x 0)
    (print (show x))
    (pure 0)))

(defn main []
  (do
    (maybe-print 42)
    (maybe-print -1)
    (maybe-print 7)))
```

The `then` branch returns `IO Int` (from `print`), so the `else` branch MUST also return `IO Int`. `(pure 0)` wraps `0` in `IO` to satisfy the type constraint. Output:
```
42
7
```

## B.13 Combining `do` and `bind!` [Uncovered S124 — was S10]

Sequencing effects and capturing results together.

```clojure
(platform stdio)
(import [primitives [*] prelude [*] platform.stdio [*]])

(defn main []
  (do
    (print "What is your name?")
    (bind! [name (read-line)]
      (do
        (print (str-concat "Hello, " name))
        (pure 0)))))
```

`do` sequences the prompt output; `bind!` captures the user's input as `name`; a nested `do` sequences the greeting with a `pure 0` exit code.
