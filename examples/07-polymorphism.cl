;; 07-polymorphism.cl -- Let-polymorphism and type variables
;;
;; Cranelisp uses Hindley-Milner type inference with let-polymorphism.
;; When a function's type is not fully determined by its body, the
;; inferred type contains type variables (a, b, c, ...).
;;
;; The identity function (defn id [x] x) has type (Fn [a] a) --
;; it accepts any type and returns the same type.
;;
;; That is what let-polymorphism BUYS you: the SAME polymorphic
;; definition can be instantiated at a DIFFERENT type at every call
;; site, in one program. `id` below is called at Int, at Bool, and at
;; String, and the compiler instantiates its type variable afresh each
;; time. This is not a REPL-only convenience — it holds in batch mode
;; exactly as it does interactively.

;; The identity function on Int: type inferred as (Fn [a] a),
;; instantiated to (Fn [Int] Int) at the call site.
(defn id [x] x)

;; Always return the first of two values.
;; Type: (Fn [a b] a)
(defn first-of [a b] a)

;; Always return the second of two values.
;; Type: (Fn [a b] b)
(defn second-of [a b] b)

;; Choose between two values based on a boolean flag.
;; Type: (Fn [Bool a a] a)
;; The flag is Bool, but x and y can be any type (as long as
;; they match each other).
(defn choose [flag x y] (if flag x y))

;; A polymorphic function can call other polymorphic functions.
;; "Apply the same value twice to first-of" -- always returns x.
(defn same-pair [x] (first-of x x))

;; Polymorphic conditional chains: nested use of choose
(defn pick-best [a b c]
  (choose (gt-i64 a b)
    (choose (gt-i64 a c) a c)
    (choose (gt-i64 b c) b c)))

;; Demonstrate type inference with multiple parameters:
;; swap uses two type variables, showing the type system tracks
;; each independently. Here we "swap" by returning second then first.
;; Note: without tuples we can only return one value, so we use
;; first-of/second-of to demonstrate the concept.
(defn use-first [] (first-of 10 20))
(defn use-second [] (second-of 10 20))

;; --- One definition, three instantiations ---

;; `id` is a single definition. Here it is used at Bool (in the `if`
;; condition), at String (fed to `str-len`), and at Int (the branch
;; value) — three different instantiations of `(Fn [a] a)` inside one
;; function body, in one batch program. `first-of` is instantiated at
;; two different type PAIRS in the same expression for good measure.
;; Contributes 1 on success.
(defn test-many-instantiations []
  (if (id true)
    (if (eq-i64 (str-len (id "abcd")) (id 4))
      (if (str-eq (first-of "yes" 0) "yes")
        (if (eq-i64 (first-of 1 false) 1) 1 0)
        0)
      0)
    0))

;; Expected: 42 + 10 + 10 + 20 + 7 + 30 + 1 = 120
(defn main []
  ;; Wrap the sum-of-pass-counts in `Pure`: every batch `main` must
  ;; return `IO _`. The inner Int is the exit code (preserved).
  (Pure
    (add-i64 (id 42)
      (add-i64 (choose true 10 20)
        (add-i64 (use-first)
          (add-i64 (use-second)
            (add-i64 (same-pair 7)
              (add-i64 (pick-best 10 30 20)
                       (test-many-instantiations)))))))))
