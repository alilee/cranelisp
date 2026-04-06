;; num/int.cl — Int operations
;;
;; Integer-specific functions built on Ring 0 primitives.
;; No remainder/modulus primitive exists, so rem is implemented
;; using truncated division: rem(a, b) = a - (a / b) * b
;;
;; Spec: plan-stdlib.md §3.3

(import [prelude []])
(import [primitives [*]])

(defn rem "Integer remainder (truncated division): a - (a / b) * b"
  [:Int a :Int b] :Int
  (sub-i64 a (mul-i64 (div-i64 a b) b)))

(defn abs "Absolute value of an integer"
  [:Int x] :Int
  (if (lt-i64 x 0) (sub-i64 0 x) x))

(defn sign "Sign of an integer: -1, 0, or 1"
  [:Int x] :Int
  (if (lt-i64 x 0) -1
    (if (gt-i64 x 0) 1 0)))

(defn negate "Negate an integer"
  [:Int x] :Int
  (sub-i64 0 x))

(defn even? "Test if an integer is even"
  [:Int x] :Bool
  (eq-i64 (rem x 2) 0))

(defn odd? "Test if an integer is odd"
  [:Int x] :Bool
  (not (eq-i64 (rem x 2) 0)))

(defn min-int "Return the smaller of two integers"
  [:Int a :Int b] :Int
  (if (lt-i64 a b) a b))

(defn max-int "Return the larger of two integers"
  [:Int a :Int b] :Int
  (if (gt-i64 a b) a b))

(defn clamp "Clamp an integer to the range [lo, hi]"
  [:Int x :Int lo :Int hi] :Int
  (if (lt-i64 x lo) lo
    (if (gt-i64 x hi) hi x)))
