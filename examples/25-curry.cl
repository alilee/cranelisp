;; 25-curry.cl -- Auto-currying and partial application
;;
;; In Cranelisp, calling a function with fewer arguments than it
;; expects returns a new function that waits for the remaining args.
;; This is called auto-currying.
;;
;; For example, a three-argument function:
;;   (defn add3 [a b c] (add-i64 a (add-i64 b c)))
;;
;; Can be partially applied:
;;   (add3 10)       ;; returns (Fn [Int Int] Int) that adds 10 to sum of two args
;;   (add3 10 20)    ;; returns (Fn [Int] Int) that adds 30 to its arg
;;
;; This enables a point-free style of programming where you build
;; specialised functions from general ones without writing lambdas.
;;
;; Currying is not limited to top-level `defn`s. It applies to any
;; function VALUE — including a closure returned from another function
;; (12-closures.cl) and a trait operator (15-traits.cl). Both are shown
;; at the end.

;; The operator traits come from the examples-local library, which is
;; just lesson 15 packaged up so this example can keep its attention on
;; currying instead of re-declaring `Num` for a third time. See
;; examples/lib/README.md.
(import [operators [Num +]])

;; --- Basic partial application ---

;; A two-argument function
(defn add [a b] (add-i64 a b))

;; Partially apply to create increment
(defn test-inc []
  (let [inc (add 1)]
    (inc 41)))

;; A three-argument function
(defn add3 [a b c] (add-i64 a (add-i64 b c)))

;; Apply one arg: get a two-arg function
(defn test-partial-one []
  (let [add-from-10 (add3 10)]
    (add-from-10 20 12)))

;; Apply two args: get a one-arg function
(defn test-partial-two []
  (let [add-30 (add3 10 20)]
    (add-30 12)))

;; --- Currying with higher-order functions ---

;; apply-twice takes a function and applies it twice
(defn apply-twice [f x] (f (f x)))

;; Use curried add with apply-twice
(defn test-curry-compose []
  (let [add5 (add 5)]
    (apply-twice add5 0)))

;; --- Building specialised functions ---

;; A general scaling function
(defn scale [factor x] (mul-i64 factor x))

;; Create specialised scalers via currying
(defn test-scalers []
  (let [double (scale 2)
        triple (scale 3)]
    (add-i64 (double 7) (triple 7))))

;; --- Curried functions as arguments ---

;; map-pair applies a function to two values and sums results
(defn map-pair [f a b] (add-i64 (f a) (f b)))

(defn test-curry-as-arg []
  (map-pair (add 100) 1 2))

;; --- Currying a function VALUE, not just a named defn ---

;; `make-adder` returns a two-argument CLOSURE that captures `base`.
;; The closure is an ordinary function value, so it curries like any
;; other: `(g 1)` supplies one of its two arguments and hands back a
;; function still waiting for the second.
;;
;; (Keep the captured value a scalar here. Auto-curried partials over
;; HEAP captures currently reach an open compiler defect, FIXME 0796.)
(defn make-adder [base] (fn [a b] (add-i64 base (add-i64 a b))))

(defn test-closure-curry []
  (let [g (make-adder 10)]
    ((g 1) 2)))                                   ;; -> 10 + 1 + 2 = 13

;; --- Currying a trait operator ---

;; `+` is a trait method (15-traits.cl), not a plain function, but at a
;; call site it is a function value like any other — so a partial
;; application works and KEEPS its dispatch. `(+ 5)` fixes the left
;; operand at Int, which is what selects the `Num Int` impl; the
;; resulting one-argument function is still that impl's `+`.
(defn test-operator-partial []
  (let [add5 (+ 5)]
    (add5 3)))                                    ;; -> 8

;; Expected: 42 + 42 + 42 + 10 + 35 + 203 + 13 + 8 = 395
;; The process EXIT CODE is the low byte of that sum: 395 mod 256 = 139.
(defn main []
  ;; Wrap the sum-of-pass-counts in `Pure`: every batch `main` must
  ;; return `IO _`. The inner Int is the exit code (preserved).
  (Pure
    (add-i64 (test-inc)
      (add-i64 (test-partial-one)
        (add-i64 (test-partial-two)
          (add-i64 (test-curry-compose)
            (add-i64 (test-scalers)
              (add-i64 (test-curry-as-arg)
                (add-i64 (test-closure-curry)
                         (test-operator-partial))))))))))
