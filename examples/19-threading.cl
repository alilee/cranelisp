;; 19-threading.cl -- Data pipelines with threading macros
;;
;; Deeply nested function calls are hard to read:
;;
;;   (str-len (str-concat "hello" (str-concat ", " "world")))
;;
;; Threading macros let you write this as a top-to-bottom pipeline:
;;
;;   (-> "hello"
;;       (str-concat ", ")
;;       (str-concat "world")    ;; NOTE: this is wrong for str-concat
;;       str-len)
;;
;; Two threading macros serve different insertion points:
;;
;;   (-> x (f a))   expands to  (f x a)    — thread as FIRST argument
;;   (->> x (f a))  expands to  (f a x)    — thread as LAST argument
;;
;; Both macros are recursive: each step's result becomes the input to the
;; next step, producing a flat pipeline from nested calls.
;;
;; This example defines -> and ->> from scratch using defmacro, then
;; demonstrates data transformation pipelines with both.

;; --- Macro machinery imports ---

;; Macros operate on Sexp (syntax tree) values. We need the constructors
;; to manipulate argument lists.
(import [macros [SexpSym SexpList SCons SNil Sexp SList]])

;; --- Threading macro definitions ---

;; Thread-first: (-> x (f a b)) becomes (f x a b)
;; If a step is a bare symbol, wrap it: (-> x f) becomes (f x)
(defmacro ->
  ([x] x)
  ([x form &rest]
    (match form
      [(SexpList items)
         (match items
           [(SCons hd tl) `(-> ~(SexpList (SCons hd (SCons x tl))) ~@rest)
            SNil `(-> ~x ~@rest)])
       _ `(-> ~(SexpList (SCons form (SCons x SNil))) ~@rest)])))

;; Thread-last: (-> x (f a b)) becomes (f a b x)
;; Appends the threaded value at the end of each form's argument list.
(defmacro ->>
  ([x] x)
  ([x form &rest]
    (match form
      [(SexpList items) `(->> ~(SexpList (macros/sconcat items (SCons x SNil))) ~@rest)
       _ `(->> ~(SexpList (SCons form (SCons x SNil))) ~@rest)])))

;; --- Trait and helper setup ---

;; Traits for polymorphic operators (same as 15-traits.cl)
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

(deftrait Eq
  (= [a b] Bool))

(impl Eq Int
  (defn = [a b] (eq-i64 a b)))

(impl Eq String
  (defn = [a b] (str-eq a b)))

(deftrait Ord
  (< [a b] Bool)
  (> [a b] Bool))

(impl Ord Int
  (defn < [a b] (lt-i64 a b))
  (defn > [a b] (lt-i64 b a)))

;; --- Thread-first examples ---

;; Thread-first inserts the value as the first argument after the function.
;; This reads top-to-bottom as "start with 5, then add 3, then multiply by 2".

(defn test-thread-first-basic []
  (-> 5
      (+ 3)
      (* 2)))                                        ;; (+ 5 3) = 8, (* 8 2) = 16

;; Without threading, this would be: (* (+ 5 3) 2)
;; With threading, each step is clear.

;; Thread-first with more steps
(defn test-thread-first-chain []
  (-> 100
      (- 20)
      (/ 4)
      (+ 1)))                                        ;; 100-20=80, 80/4=20, 20+1=21

;; Thread-first with a bare symbol (no extra args)
;; A bare symbol f is treated as (f x).
(defn negate [x] (sub-i64 0 x))

(defn test-thread-first-bare []
  (-> 7
      negate))                                       ;; (negate 7) = -7

(defn test-thread-first-bare-chain []
  (-> 42
      negate
      negate))                                       ;; negate(negate(42)) = 42

;; --- Thread-last examples ---

;; Thread-last inserts the value as the LAST argument.
;; This matters when the "data" goes in the last position.

;; With thread-last, x goes at the end: (sub-i64 100 x)
(defn test-thread-last-basic []
  (->> 10
       (sub-i64 100)
       (sub-i64 50)))                                ;; (sub-i64 100 10)=90, (sub-i64 50 90)=-40

(defn test-thread-last-negate []
  (->> 10
       (sub-i64 100)))                               ;; (sub-i64 100 10) = 90

;; --- String pipelines ---

;; String operations benefit from threading because str-concat takes
;; the base string first: (str-concat base suffix).
;; Thread-first inserts the accumulating string as the first arg.

(defn test-string-pipeline []
  (-> "hello"
      (str-concat ", ")
      (str-concat "world!")
      str-len))                                      ;; "hello, " -> "hello, world!" -> 13

;; Build a greeting string step by step
(defn test-greeting []
  (str-eq
    (-> "hello"
        (str-concat " ")
        (str-concat "cranelisp"))
    "hello cranelisp"))                              ;; true -> 1 via if

;; --- Thread-first vs thread-last comparison ---

;; The difference is WHERE the threaded value is inserted:
;;   ->  inserts as FIRST arg  (good for method-like calls)
;;   ->> inserts as LAST arg   (good for collection operations)

;; sub-i64 is not commutative, so the position matters:
;;   (-> 10 (sub-i64 3))  = (sub-i64 10 3) = 7
;;   (->> 10 (sub-i64 3)) = (sub-i64 3 10) = -7

(defn test-position-first []
  (-> 10
      (sub-i64 3)))                                  ;; (sub-i64 10 3) = 7

(defn test-position-last []
  (->> 10
       (sub-i64 3)))                                 ;; (sub-i64 3 10) = -7

;; --- Practical examples ---

;; Compute the absolute value of a negative expression via pipeline
(defn abs [x] (if (< x 0) (sub-i64 0 x) x))

(defn test-practical-pipeline []
  (-> 100
      (- 150)
      abs
      (* 3)))                                        ;; 100-150=-50, abs=50, *3=150

;; Thread-first with multiple arguments: (-> x (f a b)) becomes (f x a b).
;; Design the function with the "subject" as first parameter so threading reads
;; naturally top-to-bottom.
(defn clamp [x lo hi]
  (if (< x lo) lo (if (> x hi) hi x)))

(defn test-clamp-pipeline []
  (-> 200
      (clamp 0 100)))                                ;; (clamp 200 0 100) = 100

;; --- Sum results ---

;; test-thread-first-basic:     16
;; test-thread-first-chain:     21
;; test-thread-first-bare:      -7  (negate 7)
;; test-thread-first-bare-chain: 42
;; test-thread-last-basic:      -40
;; test-thread-last-negate:     90
;; test-string-pipeline:        13
;; test-greeting:               1 (true as int)
;; test-position-first:         7
;; test-position-last:          -7
;; test-practical-pipeline:     150
;; test-clamp-pipeline:         100
;; Total: 16+21+(-7)+42+(-40)+90+13+1+7+(-7)+150+100 = 386

(defn main []
  ;; Wrap the sum-of-pass-counts in `Pure`: every batch `main` must
  ;; return `IO _`. The inner Int is the exit code (preserved).
  (Pure
    (add-i64 (test-thread-first-basic)
      (add-i64 (test-thread-first-chain)
        (add-i64 (test-thread-first-bare)
          (add-i64 (test-thread-first-bare-chain)
            (add-i64 (test-thread-last-basic)
              (add-i64 (test-thread-last-negate)
                (add-i64 (test-string-pipeline)
                  (add-i64 (if (test-greeting) 1 0)
                    (add-i64 (test-position-first)
                      (add-i64 (test-position-last)
                        (add-i64 (test-practical-pipeline)
                                 (test-clamp-pipeline))))))))))))))
