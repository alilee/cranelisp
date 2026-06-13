;; 18-macros.cl -- Compile-time code transformation with macros
;;
;; Macros transform code at compile time. A macro receives its arguments
;; as syntax trees (Sexp values) and returns a new syntax tree that
;; replaces the macro call.
;;
;;   (defmacro name [params] body)
;;
;; The body must return a Sexp value. Quasiquote (`) makes this easy:
;;
;;   `(add-i64 ~x 1)
;;
;; The backtick (`) quotes the expression as a syntax tree.
;; The tilde (~) unquotes a variable, splicing its value into the tree.
;;
;; Without quasiquote you would have to manually construct Sexp values:
;;   (SexpList (SCons (SexpSym "add-i64") (SCons x (SCons (SexpInt 1) SNil))))
;;
;; Quasiquote is syntactic sugar for exactly that construction.
;;
;; Macros are expanded before type checking, so they can generate any
;; valid code -- new function calls, let bindings, if expressions, etc.

;; --- A simple macro: increment ---

;; my-inc adds 1 to its argument at compile time.
;; When you write (my-inc 41), the compiler replaces it with (add-i64 41 1).
(defmacro my-inc [x]
  `(add-i64 ~x 1))

(defn test-inc []
  (my-inc 41))                                           ;; -> 42

;; --- Control flow macros ---

;; when: evaluate body if condition is true, return 0 otherwise.
;; This is a common pattern -- turn a two-branch if into a one-branch form.
(defmacro when [cond body]
  `(if ~cond ~body 0))

;; unless: the opposite of when
(defmacro unless [cond body]
  `(if ~cond 0 ~body))

(defn test-when-true []
  (when true 42))                                        ;; -> 42

(defn test-when-false []
  (when false 42))                                       ;; -> 0

(defn test-unless []
  (unless false 99))                                     ;; -> 99

;; --- Boolean logic macros ---

;; Short-circuit AND: if a is false, don't evaluate b
(defmacro my-and [a b]
  `(if ~a ~b false))

;; Short-circuit OR: if a is true, don't evaluate b
(defmacro my-or [a b]
  `(if ~a true ~b))

(defn test-and-tt []
  (if (my-and true true) 1 0))                           ;; -> 1

(defn test-and-tf []
  (if (my-and true false) 1 0))                          ;; -> 0

(defn test-and-ft []
  (if (my-and false true) 1 0))                          ;; -> 0

(defn test-or-ff []
  (if (my-or false false) 1 0))                          ;; -> 0

(defn test-or-ft []
  (if (my-or false true) 1 0))                           ;; -> 1

;; --- Macros that generate let bindings ---

;; swap: evaluate two expressions and return them in opposite order
;; via a let binding to avoid double evaluation
(defmacro with-double [x body]
  `(let [doubled (add-i64 ~x ~x)] ~body))

(defn test-with-double []
  (with-double 21 doubled))                              ;; -> 42

;; --- Macros that nest other forms ---

;; A macro that computes the sum of three values using nested add-i64
(defmacro add3 [a b c]
  `(add-i64 ~a (add-i64 ~b ~c)))

(defn test-add3 []
  (add3 10 20 30))                                       ;; -> 60

;; A macro that clamps a value to zero or above
(defmacro max-zero [x]
  `(if (lt-i64 ~x 0) 0 ~x))

(defn test-max-zero-neg []
  (max-zero (sub-i64 0 7)))                              ;; -> 0

(defn test-max-zero-pos []
  (max-zero 5))                                          ;; -> 5

;; --- Multi-clause macros ---

;; Macros can have multiple clauses, dispatched by argument count.
;; The first matching clause wins.
(defmacro my-sum
  ([a] `(add-i64 ~a 0))
  ([a b] `(add-i64 ~a ~b))
  ([a b c] `(add-i64 ~a (add-i64 ~b ~c))))

(defn test-sum-1 []
  (my-sum 42))                                           ;; -> 42

(defn test-sum-2 []
  (my-sum 20 22))                                        ;; -> 42

(defn test-sum-3 []
  (my-sum 10 12 20))                                     ;; -> 42

;; --- Macros composing with other macros ---

;; Macros can expand to code that uses other macros.
;; The compiler re-expands until no macros remain.
(defmacro inc-twice [x]
  `(my-inc (my-inc ~x)))

(defn test-inc-twice []
  (inc-twice 40))                                        ;; -> 42

;; --- Macros with ADTs ---

;; Macros work with any language feature, including ADTs
(deftype (Option a) None (Some [:a val]))

(defmacro some-or [opt default]
  `(match ~opt [(Some v) v None ~default]))

(defn test-some-or-some []
  (some-or (Some 42) 0))                                 ;; -> 42

(defn test-some-or-none []
  (some-or None 99))                                     ;; -> 99

;; Expected: 42+42+0+99 + 1+0+0+0+1 + 42+60+0+5 + 42+42+42+42 + 42+99 = 601
(defn main []
  ;; Wrap the sum-of-pass-counts in `Pure`: every batch `main` must
  ;; return `IO _`. The inner Int is the exit code (preserved).
  (Pure
    (add-i64 (test-inc)
      (add-i64 (test-when-true)
        (add-i64 (test-when-false)
          (add-i64 (test-unless)
            (add-i64 (test-and-tt)
              (add-i64 (test-and-tf)
                (add-i64 (test-and-ft)
                  (add-i64 (test-or-ff)
                    (add-i64 (test-or-ft)
                      (add-i64 (test-with-double)
                        (add-i64 (test-add3)
                          (add-i64 (test-max-zero-neg)
                            (add-i64 (test-max-zero-pos)
                              (add-i64 (test-sum-1)
                                (add-i64 (test-sum-2)
                                  (add-i64 (test-sum-3)
                                    (add-i64 (test-inc-twice)
                                      (add-i64 (test-some-or-some)
                                               (test-some-or-none)))))))))))))))))))))
