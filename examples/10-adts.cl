;; 10-adts.cl -- Algebraic data types with fields
;;
;; Ring 0 introduced enum types (deftype with nullary constructors).
;; Ring 1 adds data constructors -- variants that carry values.
;;
;; Product types (all-in-one constructor with named, typed fields):
;;   (deftype Point [:Int x :Int y])
;;   Constructor: (Point 3 4) creates a Point value.
;;
;; Sum types (multiple constructors, some with fields):
;;   (deftype (Option a) None (Some [:a val]))
;;   None is a nullary constructor (no fields).
;;   (Some 42) is a data constructor carrying one field.
;;   The (Option a) syntax makes it polymorphic -- a can be any type.
;;
;; Shortcut syntax (bare field names, types inferred):
;;   (deftype Pair [first second])
;;   Equivalent to polymorphic (deftype (Pair a b) (Pair [:a first :b second])).
;;
;; Values are heap-allocated and reference-counted. Constructors are
;; called like functions. Field access requires pattern matching (next example).

;; A product type: a 2D point
(deftype Point [:Int x :Int y])

;; Construct a point and extract its x coordinate via match
(defn get-x [p]
  (match p [(Point px py) px]))

(defn get-y [p]
  (match p [(Point px py) py]))

;; Create a point and compute x + y
(defn test-point []
  (let [p (Point 3 4)]
    (add-i64 (get-x p) (get-y p))))

;; A product type with three fields
(deftype Triple [:Int a :Int b :Int c])

(defn sum-triple [t]
  (match t [(Triple a b c) (add-i64 a (add-i64 b c))]))

(defn test-triple []
  (sum-triple (Triple 10 20 30)))

;; A polymorphic sum type: Option
(deftype (Option a) None (Some [:a val]))

;; Unwrap with a default for None
(defn unwrap-or [opt default]
  (match opt
    [(Some x) x
     None     default]))

(defn test-option-some []
  (unwrap-or (Some 42) 0))

(defn test-option-none []
  (unwrap-or None 99))

;; Constructors are values -- they can be returned from functions
(defn make-some [x] (Some x))

(defn test-make-some []
  (unwrap-or (make-some 7) 0))

;; Functions that return an ADT
(defn origin [] (Point 0 0))

(defn test-origin []
  (add-i64 (get-x (origin)) (get-y (origin))))

;; A sum type with two data constructors
(deftype (Either a b) (Left [:a val]) (Right [:b val]))

(defn get-either [e]
  (match e
    [(Left x)  x
     (Right y) y]))

(defn test-either []
  (add-i64 (get-either (Left 10)) (get-either (Right 20))))

;; Shortcut syntax: bare field names, types inferred
(deftype Pair [first second])

(defn sum-pair [p]
  (match p [(Pair a b) (add-i64 a b)]))

(defn test-pair []
  (sum-pair (Pair 5 15)))

;; Expected: 7 + 60 + 42 + 99 + 7 + 0 + 30 + 20 = 265
(defn main []
  ;; Wrap the sum-of-pass-counts in `Pure`: every batch `main` must
  ;; return `IO _`. The inner Int is the exit code (preserved).
  (Pure
    (add-i64 (test-point)
      (add-i64 (test-triple)
        (add-i64 (test-option-some)
          (add-i64 (test-option-none)
            (add-i64 (test-make-some)
              (add-i64 (test-origin)
                (add-i64 (test-either)
                         (test-pair))))))))))
