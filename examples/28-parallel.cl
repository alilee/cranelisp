;; 28-parallel.cl -- Lenient evaluation (automatic parallelism)
;;
;; Cranelisp is a pure language: functions have no side effects and
;; binding order within a `let` block doesn't affect the result.
;; The compiler exploits this with LENIENT EVALUATION — independent
;; let bindings are automatically evaluated in parallel when the
;; compiler's cost heuristic determines it is beneficial.
;;
;; No language syntax is needed. You write ordinary `let` expressions
;; and the compiler does the rest:
;;
;;   1. Independence check: a binding is independent if its free
;;      variables do not include any name bound earlier in the same
;;      `let` block.
;;
;;   2. Cost heuristic: trivially cheap operations (arithmetic,
;;      variable references, constructors) are never parallelized.
;;      Only bindings whose estimated cost exceeds the threshold
;;      — typically function calls — are candidates for sparking.
;;
;;   3. Barrier: all sparked bindings are forced (waited on) before
;;      the `let` body executes, so results are always available.
;;
;; Because evaluation is pure, the parallelism is semantically
;; transparent — you get the same result whether bindings run
;; sequentially or in parallel. Programs MUST NOT depend on
;; evaluation order within a `let` block.
;;
;; Disable with: CRANELISP_NO_LENIENT=1

;; --- Expensive helper functions ---
;; These are non-trivial computations the compiler considers
;; worth sparking (they exceed the cost heuristic threshold).

;; Sum integers from 1 to n via recursion.
(defn sum-to [:Int n]
  (if (le-i64 n 0) 0
    (add-i64 n (sum-to (sub-i64 n 1)))))

;; Compute the nth Fibonacci number.
(defn fib [:Int n]
  (if (le-i64 n 1) n
    (add-i64 (fib (sub-i64 n 1))
             (fib (sub-i64 n 2)))))

;; Factorial of n.
(defn factorial [:Int n]
  (if (le-i64 n 1) 1
    (mul-i64 n (factorial (sub-i64 n 1)))))

;; --- Test 1: Independent bindings are parallelized ---
;;
;; These three bindings are independent — none references a name
;; bound by another. The compiler sparks them in parallel.
;;
;;   x depends on: sum-to (global)     -- independent
;;   y depends on: fib (global)        -- independent
;;   z depends on: factorial (global)  -- independent

(defn test-independent-let []
  (let [x (sum-to 100)          ;; = 5050
        y (fib 10)              ;; = 55
        z (factorial 5)]        ;; = 120
    (add-i64 x (add-i64 y z))))                          ;; -> 5225

;; --- Test 2: Dependent bindings stay sequential ---
;;
;; Here, `doubled` depends on `base`, so they cannot be
;; parallelized. The compiler leaves them sequential.
;;
;;   base depends on: sum-to (global)  -- independent
;;   doubled depends on: base (local)  -- DEPENDENT on base

(defn test-dependent-let []
  (let [base (sum-to 50)            ;; = 1275
        doubled (mul-i64 base 2)]   ;; = 2550
    doubled))                                             ;; -> 2550

;; --- Test 3: Cheap bindings are NOT parallelized ---
;;
;; Even when independent, trivially cheap operations (arithmetic,
;; variable references, literal values) skip the thread pool.
;; The cost heuristic avoids parallelism overhead for fast ops.

(defn test-cheap-not-sparked []
  (let [a (add-i64 1 2)       ;; cheap arithmetic — not sparked
        b (mul-i64 3 4)       ;; cheap arithmetic — not sparked
        c (sub-i64 10 1)]     ;; cheap arithmetic — not sparked
    (add-i64 a (add-i64 b c))))                          ;; -> 24

;; --- Test 4: Mixed independent and dependent ---
;;
;; In a single let block, some bindings may be independent
;; (sparkable) while others depend on earlier bindings.
;;
;;   a depends on: fib (global)       -- independent
;;   b depends on: sum-to (global)    -- independent
;;   c depends on: a, b (local)       -- DEPENDENT, sequential

(defn test-mixed []
  (let [a (fib 8)                 ;; = 21, sparked
        b (sum-to 20)             ;; = 210, sparked
        c (add-i64 a b)]          ;; = 231, sequential (depends on a, b)
    c))                                                   ;; -> 231

;; --- Test 5: Nested lets with independent bindings ---
;;
;; Each `let` is analyzed independently. The outer let sparks
;; x and y; the inner let sparks p and q.

(defn test-nested-lets []
  (let [x (sum-to 30)             ;; = 465, sparked in outer let
        y (fib 7)]                ;; = 13, sparked in outer let
    (let [p (factorial 6)         ;; = 720, sparked in inner let
          q (sum-to 10)]          ;; = 55, sparked in inner let
      (add-i64 (add-i64 x y)
               (add-i64 p q)))))                          ;; -> 1253

;; --- Verify all results ---
;;
;; Expected: 5225 + 2550 + 24 + 231 + 1253 = 9283

(defn main []
  (add-i64 (test-independent-let)
    (add-i64 (test-dependent-let)
      (add-i64 (test-cheap-not-sparked)
        (add-i64 (test-mixed)
                 (test-nested-lets))))))
