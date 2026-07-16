;; 36-multi-arity.cl -- Multi-signature functions (defn dispatch)
;;
;; A single `defn` may carry SEVERAL clauses, each a `([params] body)`
;; form. The name resolves to whichever clause matches the call site.
;; This is the FUNCTION-level counterpart to the multi-clause `defmacro`
;; seen in 18/19, and it is spec-settled in §5.1.2 ("Multi-Signature").
;;
;;   (defn scale
;;     ([x]   (mul-i64 x 2))     ;; 1-arg clause
;;     ([x y] (mul-i64 x y)))    ;; 2-arg clause
;;
;; Two kinds of dispatch appear below:
;;
;;   1. ARITY dispatch  -- clauses differ by NUMBER of parameters.
;;      `(scale 5)` picks the 1-arg clause; `(scale 3 4)` the 2-arg one.
;;
;;   2. TYPE dispatch   -- clauses share an arity but differ by the
;;      CONCRETE type of a parameter (`:Int` vs `:Blob` vs `:(Vec Int)`).
;;      Dispatch is resolved statically, after type inference.
;;
;; Relationship to currying (25): auto-currying partially applies ONE
;; signature; multi-signature dispatch selects AMONG several clauses.
;; When a clause matches the call's arity, that clause is chosen -- arity
;; dispatch takes precedence over currying. `(scale 5)` runs the 1-arg
;; clause (=> 10); it does NOT curry the 2-arg clause.
;;
;; Clause independence (§5.1.2): each clause is type-checked on its own.
;; A clause's parameters are NOT pinned by a sibling clause, so a clause
;; whose parameters inference cannot pin from its OWN body needs its own
;; annotations. That is why the type-dispatch and default-supplying
;; clauses below annotate every parameter.
;;
;; Every sub-test returns 1 on pass and 0 on failure; `main` sums them,
;; so the exit code is the number of passing sub-tests.
;;
;; Expected exit code: 8 (all eight sub-tests pass).

;; The `:(Vec Int)` clause below annotates a parameter with the `Vec`
;; TYPE, so the type name must be in scope. The examples prelude
;; re-exports the vec-* FUNCTIONS but not the type, so import it here.
(import [primitives [Vec]])

;; Bool -> Int: 1 when the computed value equals the expected one.
(defn pass [actual expected]
  (if (eq-i64 actual expected) 1 0))

;; --- 1. Arity dispatch: same name, different parameter counts ---

(defn scale
  ([x]     (mul-i64 x 2))               ;; 1 arg: double it
  ([x y]   (mul-i64 x y))               ;; 2 args: product
  ([x y z] (add-i64 (mul-i64 x y) z)))  ;; 3 args: multiply-then-add

(defn test-arity-one []   (pass (scale 5)      10))  ;; 5*2
(defn test-arity-two []   (pass (scale 3 4)    12))  ;; 3*4
(defn test-arity-three [] (pass (scale 2 3 7)  13))  ;; 2*3+7

;; --- 2. Type dispatch: same arity (1), different concrete types ---

(deftype Blob (MkBlob [:Int n]))

;; Each clause must annotate its parameter: clauses are checked
;; independently, so `x`/`b`/`v` cannot borrow a type from a sibling.
(defn measure
  ([:Int x]       x)
  ([:Blob b]      (match b [(MkBlob n) n]))
  ([:(Vec Int) v] (vec-len v)))

(defn test-type-int []  (pass (measure 5)          5))
(defn test-type-blob [] (pass (measure (MkBlob 9)) 9))
(defn test-type-vec []  (pass (measure [1 2 3 4])  4))  ;; length 4

;; --- 3. Arity-overload for defaults (the classic idiom) ---
;;
;; A shorter clause supplies a default argument and DELEGATES to a longer
;; clause -- the same name, one arity calling another. `between` sums the
;; integers in [lo, hi] stepping by `by`; the 2-arg clause defaults the
;; step to 1 and hands off to the 3-arg clause, which recurses.

(defn between
  ([:Int lo :Int hi]         (between lo hi 1))
  ([:Int lo :Int hi :Int by] (if (le-i64 lo hi)
                               (add-i64 lo (between (add-i64 lo by) hi by))
                               0)))

(defn test-default-step []  (pass (between 1 3)   6))   ;; 1+2+3
(defn test-explicit-step [] (pass (between 0 6 2) 12))  ;; 0+2+4+6

;; --- Summing sub-test results ---
;;
;; Eight sub-tests, each contributing 1 on pass. `main` calls the
;; overloaded `scale`/`measure`/`between` directly -- exactly the shape
;; (an entry `main` whose body calls an overloaded fn) that dispatches
;; and returns cleanly, with the same exit code under `--run` and
;; `--link`.
(defn main []
  (Pure
    (add-i64 (test-arity-one)
      (add-i64 (test-arity-two)
        (add-i64 (test-arity-three)
          (add-i64 (test-type-int)
            (add-i64 (test-type-blob)
              (add-i64 (test-type-vec)
                (add-i64 (test-default-step)
                         (test-explicit-step))))))))))
