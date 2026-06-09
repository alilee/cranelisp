;; 15-traits.cl -- Trait-based operator dispatch and constrained polymorphism
;;
;; Cranelisp defines traits for operator dispatch. This example declares
;; the Num, Eq, and Ord traits and their implementations for Int and Float
;; (Eq also for Bool and String). The operators dispatch to the correct
;; implementation based on the types of their arguments.
;;
;; Functions that use trait operators become constrained polymorphic:
;; (defn double [x] (+ x x)) works on any Num type. The compiler
;; monomorphises such functions at each call site.
;;
;; Prior examples used monomorphic named primitives like add-i64
;; and eq-i64. Trait operators replace those with polymorphic
;; versions: (+ 1 2) and (+ 1.5 2.5) both use +, dispatched by type.
;;
;; Named primitives remain available (the transition is accretive).

;; --- Trait declarations and implementations ---

(deftrait Num
  (+ [a b] self)
  (- [a b] self)
  (* [a b] self)
  (/ [a b] self))

(impl Num Int
  (defn + [a b] (add-i64 a b))
  (defn - [a b] (sub-i64 a b))
  (defn * [a b] (mul-i64 a b))
  (defn / [a b] (div-i64 a b)))

(impl Num Float
  (defn + [a b] (add-f64 a b))
  (defn - [a b] (sub-f64 a b))
  (defn * [a b] (mul-f64 a b))
  (defn / [a b] (div-f64 a b)))

(deftrait Eq
  (= [a b] Bool)
  (!= [a b] Bool))

(impl Eq Int
  (defn = [a b] (eq-i64 a b))
  (defn != [a b] (not (eq-i64 a b))))

(impl Eq Float
  (defn = [a b] (eq-f64 a b))
  (defn != [a b] (not (eq-f64 a b))))

(impl Eq Bool
  (defn = [a b] (eq-bool a b))
  (defn != [a b] (not (eq-bool a b))))

(impl Eq String
  (defn = [a b] (str-eq a b))
  (defn != [a b] (not (str-eq a b))))

(deftrait Ord
  (< [a b] Bool)
  (> [a b] Bool)
  (<= [a b] Bool)
  (>= [a b] Bool))

(impl Ord Int
  (defn < [a b] (lt-i64 a b))
  (defn > [a b] (lt-i64 b a))
  (defn <= [a b] (not (lt-i64 b a)))
  (defn >= [a b] (not (lt-i64 a b))))

(impl Ord Float
  (defn < [a b] (lt-f64 a b))
  (defn > [a b] (lt-f64 b a))
  (defn <= [a b] (not (lt-f64 b a)))
  (defn >= [a b] (not (lt-f64 a b))))

;; --- Num trait: arithmetic on Int ---

(defn test-plus-int [] (+ 3 4))                      ;; -> 7
(defn test-minus-int [] (- 10 3))                     ;; -> 7
(defn test-mul-int [] (* 6 7))                        ;; -> 42
(defn test-div-int [] (/ 20 4))                       ;; -> 5

;; Nested arithmetic using trait operators
(defn test-nested-arith [] (* (+ 2 3) (- 10 4)))     ;; -> 30

;; --- Num trait: arithmetic on Float ---

;; The same operators work for floats. The type checker infers which
;; Num impl to use from the operand types.
;; We compare results to known values using the named primitive eq-f64,
;; since Float results must be converted to Int for the final sum.
(defn test-plus-float []
  (if (eq-f64 (+ 1.5 2.5) 4.0) 1 0))                ;; -> 1

(defn test-mul-float []
  (if (eq-f64 (* 3.0 4.0) 12.0) 1 0))               ;; -> 1

;; --- Eq trait: equality ---

;; = works on Int, Float, Bool, and String.
;; Each call dispatches to the correct Eq implementation.
(defn test-eq-int []
  (if (= 42 42) 1 0))                                ;; -> 1

(defn test-eq-float []
  (if (= 3.14 3.14) 1 0))                            ;; -> 1

(defn test-eq-bool []
  (if (= true true) 1 0))                            ;; -> 1

(defn test-eq-string []
  (if (= "hello" "hello") 1 0))                      ;; -> 1

;; Equality returns false for different values
(defn test-eq-false []
  (if (= 1 2) 1 0))                                  ;; -> 0

;; --- Ord trait: ordering ---

;; < works on Int and Float.
(defn test-lt-int []
  (if (< 3 5) 1 0))                                  ;; -> 1

(defn test-lt-float []
  (if (< 1.0 2.0) 1 0))                              ;; -> 1

(defn test-lt-false []
  (if (< 10 5) 1 0))                                 ;; -> 0

;; --- Trait operators in recursive functions ---

;; Factorial using trait operators instead of named primitives.
;; Compare with 05-recursion.cl which used mul-i64, sub-i64, eq-i64.
(defn fact [n]
  (if (= n 0) 1 (* n (fact (- n 1)))))

(defn test-factorial []
  (if (eq-i64 (fact 10) 3628800) 1 0))               ;; -> 1

;; Tail-recursive sum using trait operators
(defn sum-to [n]
  (if (= n 0) 0 (+ n (sum-to (- n 1)))))

(defn test-sum-to []
  (if (eq-i64 (sum-to 100) 5050) 1 0))               ;; -> 1

;; --- Trait operators with closures ---

;; Trait operators inside a closure capture context naturally.
(defn test-closure-op []
  (let [n 10]
    ((fn [x] (+ n x)) 32)))                           ;; -> 42

;; --- Trait operators with ADTs ---

;; Trait operators in match bodies work the same as anywhere else.
(deftype Point [:Int x :Int y])

(defn distance-sq [p]
  (match p
    [(Point x y) (+ (* x x) (* y y))]))

(defn test-adt-ops []
  (distance-sq (Point 3 4)))                          ;; -> 25

;; --- Constrained polymorphic functions ---

;; A function using a trait operator becomes constrained polymorphic:
;; its type contains a trait bound. The compiler monomorphises it at
;; each call site, generating specialised code for the concrete type.
;;
;; In the REPL:
;;   > (defn double [x] (+ x x))
;;   :(Fn [:Num a a] a) user/double
;;   > (double 21)
;;   :primitives/Int 42
;;   > (double 2.5)
;;   :primitives/Float 5.0

;; double: (+ x x) constrains x to Num
(defn double [x] (+ x x))

;; Called at Int — the compiler generates double$Int
(defn test-double-int [] (double 21))                 ;; -> 42

;; square: (* x x) also constrains x to Num
(defn square [x] (* x x))

;; Called at Int — the compiler generates square$Int
(defn test-square-int [] (square 7))                  ;; -> 49

;; Constrained functions compose: sum-of-squares uses both + and *
(defn sum-of-sq [x y] (+ (square x) (square y)))

(defn test-sum-of-sq [] (sum-of-sq 3 4))              ;; -> 25

;; --- Ord and Eq derived methods ---

;; The Ord trait provides >, <=, >= alongside <.
;; The Eq trait provides != alongside =.
;; Each method has an explicit implementation.

(defn test-gt []
  (if (> 5 3) 1 0))                                  ;; -> 1

(defn test-lte-equal []
  (if (<= 3 3) 1 0))                                 ;; -> 1

(defn test-lte-less []
  (if (<= 2 3) 1 0))                                 ;; -> 1

(defn test-gte-equal []
  (if (>= 5 5) 1 0))                                 ;; -> 1

(defn test-gte-false []
  (if (>= 4 5) 1 0))                                 ;; -> 0

;; The Eq trait provides != (not equal) alongside =.

(defn test-neq-true []
  (if (!= 1 2) 1 0))                                 ;; -> 1

(defn test-neq-false []
  (if (!= 3 3) 1 0))                                 ;; -> 0

;; --- Named primitives still work ---

;; The transition is accretive: add-i64, mul-i64, etc. remain available
;; alongside the trait-dispatched operators.
(defn test-named-prim []
  (add-i64 (mul-i64 3 3) (mul-i64 4 4)))             ;; -> 25

;; --- Sum all results ---

;; Expected: 7+7+42+5+30 + 1+1 + 1+1+1+1+0 + 1+1+0 + 1+1 + 42+25+25
;;         + 42+49+25 + 1+1+1+1+0 + 1+0 = 314
(defn main []
  (add-i64 (test-plus-int)
    (add-i64 (test-minus-int)
      (add-i64 (test-mul-int)
        (add-i64 (test-div-int)
          (add-i64 (test-nested-arith)
            (add-i64 (test-plus-float)
              (add-i64 (test-mul-float)
                (add-i64 (test-eq-int)
                  (add-i64 (test-eq-float)
                    (add-i64 (test-eq-bool)
                      (add-i64 (test-eq-string)
                        (add-i64 (test-eq-false)
                          (add-i64 (test-lt-int)
                            (add-i64 (test-lt-float)
                              (add-i64 (test-lt-false)
                                (add-i64 (test-factorial)
                                  (add-i64 (test-sum-to)
                                    (add-i64 (test-closure-op)
                                      (add-i64 (test-adt-ops)
                                        (add-i64 (test-named-prim)
                                          (add-i64 (test-double-int)
                                            (add-i64 (test-square-int)
                                              (add-i64 (test-sum-of-sq)
                                                (add-i64 (test-gt)
                                                  (add-i64 (test-lte-equal)
                                                    (add-i64 (test-lte-less)
                                                      (add-i64 (test-gte-equal)
                                                        (add-i64 (test-gte-false)
                                                          (add-i64 (test-neq-true)
                                                            (test-neq-false)))))))))))))))))))))))))))))))
