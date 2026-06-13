# Appendix B: Example Programs

Complete, runnable example programs demonstrating Cranelisp features. All examples assume the reference implementation's standard library (prelude) is available, including: the `do`, `bind!`, `list`, `cond`, `str`, `->`, `->>`, and `vec` macros; `pure`, `bind`, `show`, `parse-int`, and `str-concat` functions; `Option`, `List`, and `Seq` types; and the `Num`, `Eq`, `Ord`, `Display`, and `Functor` traits. See [Section 8.8.3](08-modules.md#883-empty-prelude) — an empty prelude is valid; the examples would require adjustment without prelude support.

## B.1 Hello World [S10]

The minimal Cranelisp program.

```clojure
(platform stdio)
(import [platform.stdio [*]])

(defn main []
  (print (show 42)))
```

Output: `42`

## B.2 Factorial (Recursion) [S10]

Recursive function with conditional and arithmetic.

```clojure
(platform stdio)
(import [platform.stdio [*]])

(defn fact [n]
  (if (= n 0)
    1
    (* n (fact (- n 1)))))

(defn main []
  (print (show (fact 10))))
```

Output: `3628800`

## B.3 Algebraic Data Types [S10]

Product types, sum types, enums, pattern matching, and trait implementations for ADTs.

```clojure
(platform stdio)
(import [platform.stdio [*]])

;; Product type (struct-like)
(deftype Point [:Int x :Int y])

;; Sum type (tagged union)
(deftype (Option a) None (Some [:a val]))

;; Enum (all-nullary sum type)
(deftype Color Red Green Blue)

;; Shortcut syntax (polymorphic product)
(deftype Pair [first second])

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
    [None default
     (Some x) x]))

;; Trait impl for enum ADT
(impl Display Color
  (defn show [c]
    (match c
      [Red "Red"
       Green "Green"
       Blue "Blue"])))

;; Polymorphic trait impl
(impl Display (Option :Display a)
  (defn show [self]
    (match self
      [None "None"
       (Some x) (show x)])))

(defn main []
  (do
    (print (show (get-x (Point 3 4))))
    (print (show (color-value Green)))
    (print (show (unwrap-or (Some 42) 0)))
    (print (show (unwrap-or None 99)))
    (print (show Red))
    (print (show (Some 42)))
    (print (show (Some 3.14)))))
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

## B.4 IO with bind! [S10]

Reading input, parsing, and error handling with monadic IO.

```clojure
(platform stdio)
(import [platform.stdio [*]])

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

## B.5 Lazy Sequences [S17]

Infinite sequences, lazy operations, and the unified collection API.

```clojure
(platform stdio)
(import [platform.stdio [*]])

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

## B.6 Macros [S17]

Compile-time code transformation with `defmacro`.

```clojure
(platform stdio)
(import [platform.stdio [*]])

;; A simple macro: wraps expression in (+ expr 1)
(defmacro my-inc [x]
  (SexpList (slist (SexpSym "+") x (SexpInt 1))))

;; Using quasiquote for cleaner syntax
(defmacro when [cond body]
  `(if ~cond ~body 0))

;; Variadic macro
(defmacro my-add [& args]
  `(+ ~@args))

(defn main []
  (do
    (print (show (my-inc 41)))       ; → 42
    (print (show (when true 99)))    ; → 99
    (print (show (my-add 10 20)))))  ; → 30
```

## B.7 Higher-Order Functions and Closures [S17]

First-class functions, closures, and auto-currying.

```clojure
(platform stdio)
(import [platform.stdio [*]])

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

## B.8 Threading Macros [S17]

Data transformation pipelines with `->` and `->>`.

```clojure
(platform stdio)
(import [platform.stdio [*]])

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

## B.9 Multi-Signature Dispatch [S17]

Functions with multiple implementations dispatched by argument type.

```clojure
(platform stdio)
(import [platform.stdio [*]])

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

## B.10 Constrained Polymorphism [S10]

Functions that work across types sharing a trait.

```clojure
(platform stdio)
(import [platform.stdio [*]])

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

## B.11 IO Sequencing with `do` [S10]

Evaluating multiple IO actions, discarding intermediate results.

```clojure
(platform stdio)
(import [platform.stdio [*]])

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

## B.12 Conditional IO with `pure` [S10]

Using `pure` to satisfy branch type requirements.

```clojure
(platform stdio)
(import [platform.stdio [*]])

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

## B.13 Combining `do` and `bind!` [S10]

Sequencing effects and capturing results together.

```clojure
(platform stdio)
(import [platform.stdio [*]])

(defn main []
  (do
    (print "What is your name?")
    (bind! [name (read-line)]
      (do
        (print (str-concat "Hello, " name))
        (pure 0)))))
```

`do` sequences the prompt output; `bind!` captures the user's input as `name`; a nested `do` sequences the greeting with a `pure 0` exit code.
